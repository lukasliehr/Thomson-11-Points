module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The Thomson problem for 11 points: the statement

This file contains the statement of the theorem and nothing else. It uses the real numbers, finite
sums, the square root and the orthogonal group of Mathlib, and no file of the library `CAP`.

**The candidate.** The minimizer of the Coulomb energy of eleven points on the unit sphere of `ℝ³`
has no closed form. `Xdec` is a configuration with decimal coordinates of fifteen places: the
reference configuration of the local constants (`N11/Local`, statement (G7)), rounded. Its points
lie on the unit sphere up to `2 · 10⁻¹⁵`.

**The theorem** (`Thomson11`). There is a configuration `X` of eleven distinct points of the unit
sphere with the following properties. Every coordinate of `X` differs from that of `Xdec` by at
most `10⁻¹⁰`. The energy of `X` lies in the interval `(40.59644951, 40.59645051]`. Every
configuration `x` of eleven distinct points of the unit sphere satisfies `energy X ≤ energy x`, and
if equality holds, then `x` arises from `X` by an orthogonal map and a relabelling of the points.
Here `energy x = ∑_{i < j} 1 / |x i - x j|` is the Coulomb energy.

So the theorem states that a minimizer exists, that it is unique up to orthogonal maps and
relabelling, and where it lies. The hypothesis that the points of `x` are distinct is needed in
this form: for two equal points Lean evaluates `1 / 0` to `0`, whereas the energy of such a
configuration is infinite.

Numerically the least energy is `40.59645050819…`, and the minimizer has the symmetry group `C2v`.
The symmetry and a sharper enclosure of the least energy are not parts of the statement below. The
file states the theorem as a proposition. Its proof is `N11.T6A.thomson11` in
`Certificates/Theorem/T6A.lean`, and `Showcase_WithProofs.lean` restates the theorem for points of the
Euclidean space.
-/

@[expose] public section

namespace N11

open Finset

/-- The Coulomb energy of `N` points of `ℝ³` that are given by their coordinates. -/
noncomputable def energy {N : ℕ} (x : Fin N → Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ j with i < j, 1 / Real.sqrt (∑ k, (x i k - x j k) ^ 2)

/-- All points lie on the unit sphere. -/
def OnSphere {N : ℕ} (x : Fin N → Fin 3 → ℝ) : Prop := ∀ i, ∑ k, x i k ^ 2 = 1

/-- The configuration `y` arises from `x` by an orthogonal map and a relabelling of the points. -/
def Congruent {N : ℕ} (x y : Fin N → Fin 3 → ℝ) : Prop :=
  ∃ U ∈ Matrix.orthogonalGroup (Fin 3) ℝ, ∃ σ : Equiv.Perm (Fin N), ∀ i, y i = U.mulVec (x (σ i))

/-- The coordinates of the candidate in units of `10⁻¹⁵`. -/
def XdecZ : Fin 11 → Fin 3 → ℤ :=
  ![![313620689025589, 319317483958265, 894247397454238],
    ![122131934022939, -879707882375786, 459562653375714],
    ![836384234608648, 540732019932700, 89834819071496],
    ![-829513636587083, -542301295299786, -133478207330809],
    ![-566960498580477, 239819275605855, -788062502659060],
    ![61432238616290, -754530255111397, -653383634766071],
    ![-16529763516812, 987228274258469, -158452205483935],
    ![892049358244038, -450479658797258, 36276982596482],
    ![482848954144595, 189339586942292, -854989712393075],
    ![-513162273240149, -211638860342633, 831789320751279],
    ![-786447187737911, 558000050679941, 264833465295296]]

/-- **The candidate**, with decimal coordinates of fifteen places. -/
noncomputable def Xdec (i : Fin 11) (k : Fin 3) : ℝ := (XdecZ i k : ℝ) / 10 ^ 15

/-- **The theorem for 11 points** (`T6`), as a proposition: the Coulomb energy of eleven points on
the unit sphere has a minimizer within `10⁻¹⁰` of the candidate, its energy lies in the interval
`(40.59644951, 40.59645051]`, and it is the only minimizer up to orthogonal maps and relabelling. -/
def Thomson11 : Prop :=
  ∃ X : Fin 11 → Fin 3 → ℝ,
    OnSphere X ∧ Function.Injective X ∧ (∀ i k, |X i k - Xdec i k| ≤ 1 / 10 ^ 10) ∧
      (4059644951 : ℝ) / 10 ^ 8 < energy X ∧ energy X ≤ 4059645051 / 10 ^ 8 ∧
        ∀ x : Fin 11 → Fin 3 → ℝ, OnSphere x → Function.Injective x →
          energy X ≤ energy x ∧ (energy x = energy X → Congruent X x)

end N11
