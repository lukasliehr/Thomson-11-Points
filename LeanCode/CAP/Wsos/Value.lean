module

public import Mathlib.Algebra.BigOperators.Ring.List
public import CAP.Wsos.Lists

/-!
# What the data of a triple type mean

The data of `CAP.Wsos.Ty` define expressions in three variables. They are written here once, over
an arbitrary commutative ring `A`: for `A = ℤ[x, y, z]` they are the polynomials for which the
numbers of the checker stand, and for `A = ℝ` they are the values in the statement of soundness.
A homomorphism of rings maps the expressions over `A` to the expressions over its target
(`map_*`), so the equation between polynomials that the checker verifies becomes an equation
between real numbers.

All expressions are homogeneous: `E` stands for `2 ^ m`, and a variable `w` stands for
`2 ^ m` times an inner product. Thus `hpow E w n i = E ^ (n - i) * w ^ i` is `E ^ n` times the
`i`-th power of the inner product.
-/

@[expose] public section

namespace CAP.Wsos

open Finset

variable {A : Type*} [CommRing A]

/-- The variable of a box: `rho * x + cp - cn`. -/
def affV (b : Box) (x : A) : A := (b.rho : A) * x + (b.cp : A) - (b.cn : A)

/-- `E ^ (n - i) * w ^ i` -/
def hpow (E w : A) (n i : ℕ) : A := E ^ (n - i) * w ^ i

/-- The polynomial of degree `n` whose coefficients are the signed digits of `c`. -/
def spolyV (wd : ℕ) (E w : A) (n c : ℕ) : A := ∑ i ∈ range (n + 1), (sdig wd c i : A) * hpow E w n i

/-- The bilinear form of a block of a Gram matrix: entry `(i, j)` is the signed digit `N * j + i` of `Gr`. -/
def bilV (wG : ℕ) (E w1 w2 : A) (n N Gr : ℕ) : A :=
  ∑ j ∈ range (n + 1), hpow E w2 n j * ∑ i ∈ range (n + 1), (sdig wG Gr (N * j + i) : A) * hpow E w1 n i

/-- The Gram matrix `G`, shifted to its block `(b, c)`. -/
def blockOf (P : Params) (G n b c : ℕ) : ℕ :=
  Nat.shiftRight G (Nat.mul P.wG (Nat.add (Nat.mul b (Nat.succ n)) (Nat.mul (Nat.mul P.q (Nat.succ n)) (Nat.mul c (Nat.succ n)))))

/-- The pair `(R (k - 1), R k)` of the kernels with `R (k + 1) = (2 k + 1) Ah R k - k ^ 2 Wh R (k - 1)`. -/
def qPair (Ah Wh : A) : ℕ → A × A
  | 0 => (0, 1)
  | k + 1 => ((qPair Ah Wh k).2,
      ((2 * k + 1 : ℕ) : A) * Ah * (qPair Ah Wh k).2 - ((k * k : ℕ) : A) * Wh * (qPair Ah Wh k).1)

/-- The kernel `R k = k! * Q k`, homogeneous. -/
def qV (Ah Wh : A) (k : ℕ) : A := (qPair Ah Wh k).2

/-- `E * w3 - w1 * w2`: `E ^ 2` times `t - u * v`. -/
def AhV (E w1 w2 w3 : A) : A := E * w3 - w1 * w2

/-- `(E ^ 2 - w1 ^ 2) * (E ^ 2 - w2 ^ 2)`: `E ^ 4` times `(1 - u ^ 2) * (1 - v ^ 2)`. -/
def WhV (E w1 w2 : A) : A := (E ^ 2 - w1 ^ 2) * (E ^ 2 - w2 ^ 2)

/-- A rooted form, multiplied by `d!` and homogeneous of degree `2 * d`. -/
noncomputable def rootedV (P : Params) (E w1 w2 w3 : A) (R : Rooted) : A :=
  ∑ k ∈ range R.gram.length, (((facts P.d).getD k 0 : ℕ) : A) * (qV (AhV E w1 w2 w3) (WhV E w1 w2) k
    * bilV P.wG E w1 w2 (P.d - k) (P.q * (P.d - k + 1)) (blockOf P (R.gram.getD k 0) (P.d - k) R.b R.c))

/-- `∑ j, (∑ i, signed digit (N * j + i)) * E ^ (d - j) * w ^ j` -/
def linV (wG : ℕ) (E w : A) (d N Gr : ℕ) : A :=
  ∑ j ∈ range (d + 1), (∑ i ∈ range (d + 1), (sdig wG Gr (N * j + i) : A)) * hpow E w d j

/-- The polynomial of the rooted blocks of a class at coinciding points, homogeneous of degree `2 * d`. -/
def rootUseV (P : Params) (E w : A) (Ru : RootUse) : A :=
  2 * E ^ P.d * linV P.wG E w P.d (P.q * (P.d + 1)) (blockOf P (Ru.gram.getD 0 0) P.d Ru.self Ru.other)
    + ∑ k ∈ range Ru.gram.length, (E ^ 2 - w ^ 2) ^ k
        * bilV P.wG E w w (P.d - k) (P.q * (P.d - k + 1)) (blockOf P (Ru.gram.getD k 0) (P.d - k) Ru.other Ru.other)

/-- `mult` times a share, in the unit of the checker and homogeneous of degree `D`. -/
def shareV (P : Params) (E w : A) (S : Share) : A :=
  2 ^ P.aP * (spolyV P.wP E w P.D S.pos
      - ∑ j ∈ range S.negs.length, ((S.negm.getD j 0 : ℕ) : A) * spolyV P.wP E w P.D (S.negs.getD j 0))
    - 2 ^ P.aF * (S.roots.map (rootUseV P E w)).sum

/-- A term of a generator, homogeneous of degree `deg`. -/
def termV (E u v t : A) (deg : ℕ) (τ : Term) : A :=
  ((τ.cp : A) - (τ.cn : A)) * (E ^ (deg - (τ.e1 + τ.e2 + τ.e3)) * (u ^ τ.e1 * v ^ τ.e2 * t ^ τ.e3))

/-- A generator of the domain, homogeneous of degree `deg`. -/
def genV (E u v t : A) (g : Gen) : A := (g.terms.map (termV E u v t g.deg)).sum

/-- A weight: the product of its generators. -/
def gensV (E u v t : A) (gs : List Gen) : A := (gs.map (genV E u v t)).prod

/-- The left-hand side of the identity of a triple type, in the unit of the checker. -/
noncomputable def lamV (P : Params) (T : Ty) (E u v t : A) : A :=
  ((fact P.d : ℕ) : A) * (((T.s2.mult * T.s3.mult : ℕ) : A) * shareV P E u T.s1
      + ((T.s1.mult * T.s3.mult : ℕ) : A) * shareV P E v T.s2 + ((T.s1.mult * T.s2.mult : ℕ) : A) * shareV P E t T.s3)
    - 2 ^ P.aF * ((2 * (T.s1.mult * T.s2.mult * T.s3.mult) : ℕ) : A)
      * (rootedV P E u v t T.r1 + rootedV P E u t v T.r2 + rootedV P E v t u T.r3)

/-- The Chebyshev polynomials: `1, x, 2 x T (n + 1) - T n`. -/
def tV (x : A) : ℕ → A
  | 0 => 1
  | 1 => x
  | n + 2 => 2 * x * tV x (n + 1) - tV x n

/-- `∑ i < n, (slot i of Cr) * T i (x)` -/
def chInV (wN : ℕ) (x : A) (n Cr : ℕ) : A := ∑ i ∈ range n, ((slot wN Cr i : ℕ) : A) * tV x i

/-- The part of a Chebyshev combination with a fixed index of `z`: `j` rows, the first one for `T k2 (y)`. -/
def chMidV (wN : ℕ) (x y : A) : ℕ → ℕ → ℕ → A
  | 0, _, _ => 0
  | j + 1, k2, Cr => tV y k2 * chInV wN x (j + 1) Cr + chMidV wN x y j (k2 + 1) (Cr >>> (wN * (j + 1)))

/-- A Chebyshev combination: `j` layers, the first one for `T k3 (z)`. -/
def chOutV (wN : ℕ) (x y z : A) : ℕ → ℕ → ℕ → A
  | 0, _, _ => 0
  | j + 1, k3, Cr => tV z k3 * chMidV wN x y (j + 1) 0 Cr
      + chOutV wN x y z j (k3 + 1) (Cr >>> (wN * ((j + 1) * (j + 2) / 2)))

/-! ## Homomorphisms -/

section Map

variable {A' : Type*} [CommRing A'] (φ : A →+* A')

theorem map_affV (b : Box) (x : A) : φ (affV b x) = affV b (φ x) := by simp [affV]

theorem map_hpow (E w : A) (n i : ℕ) : φ (hpow E w n i) = hpow (φ E) (φ w) n i := by simp [hpow]

theorem map_spolyV (wd : ℕ) (E w : A) (n c : ℕ) : φ (spolyV wd E w n c) = spolyV wd (φ E) (φ w) n c := by
  simp [spolyV, map_hpow]

theorem map_bilV (wG : ℕ) (E w1 w2 : A) (n N Gr : ℕ) :
    φ (bilV wG E w1 w2 n N Gr) = bilV wG (φ E) (φ w1) (φ w2) n N Gr := by
  simp [bilV, map_hpow]

theorem map_qPair (Ah Wh : A) : ∀ k, (φ (qPair Ah Wh k).1, φ (qPair Ah Wh k).2) = qPair (φ Ah) (φ Wh) k
  | 0 => by simp [qPair]
  | k + 1 => by
    have h := map_qPair Ah Wh k
    rw [Prod.ext_iff] at h
    simp only [qPair, map_sub, map_mul, map_natCast]
    rw [← h.1, ← h.2]

theorem map_qV (Ah Wh : A) (k : ℕ) : φ (qV Ah Wh k) = qV (φ Ah) (φ Wh) k := by
  have h := map_qPair φ Ah Wh k
  rw [Prod.ext_iff] at h
  exact h.2

theorem map_AhV (E w1 w2 w3 : A) : φ (AhV E w1 w2 w3) = AhV (φ E) (φ w1) (φ w2) (φ w3) := by simp [AhV]

theorem map_WhV (E w1 w2 : A) : φ (WhV E w1 w2) = WhV (φ E) (φ w1) (φ w2) := by simp [WhV]

theorem map_rootedV (P : Params) (E w1 w2 w3 : A) (R : Rooted) :
    φ (rootedV P E w1 w2 w3 R) = rootedV P (φ E) (φ w1) (φ w2) (φ w3) R := by
  simp [rootedV, map_qV, map_AhV, map_WhV, map_bilV]

theorem map_linV (wG : ℕ) (E w : A) (d N Gr : ℕ) : φ (linV wG E w d N Gr) = linV wG (φ E) (φ w) d N Gr := by
  simp [linV, map_hpow]

theorem map_rootUseV (P : Params) (E w : A) (Ru : RootUse) :
    φ (rootUseV P E w Ru) = rootUseV P (φ E) (φ w) Ru := by
  simp [rootUseV, map_linV, map_bilV, map_ofNat]

theorem map_shareV (P : Params) (E w : A) (S : Share) : φ (shareV P E w S) = shareV P (φ E) (φ w) S := by
  simp only [shareV, map_sub, map_mul, map_pow, map_ofNat, map_sum, map_natCast, map_spolyV, map_list_sum,
    List.map_map]
  congr 2
  refine congrArg List.sum (List.map_congr_left fun Ru _ => ?_)
  exact map_rootUseV φ P E w Ru

theorem map_termV (E u v t : A) (deg : ℕ) (τ : Term) :
    φ (termV E u v t deg τ) = termV (φ E) (φ u) (φ v) (φ t) deg τ := by simp [termV]

theorem map_genV (E u v t : A) (g : Gen) : φ (genV E u v t g) = genV (φ E) (φ u) (φ v) (φ t) g := by
  simp only [genV, map_list_sum, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun τ _ => map_termV φ E u v t g.deg τ)

theorem map_gensV (E u v t : A) (gs : List Gen) : φ (gensV E u v t gs) = gensV (φ E) (φ u) (φ v) (φ t) gs := by
  simp only [gensV, map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun g _ => map_genV φ E u v t g)

theorem map_lamV (P : Params) (T : Ty) (E u v t : A) :
    φ (lamV P T E u v t) = lamV P T (φ E) (φ u) (φ v) (φ t) := by
  simp [lamV, map_shareV, map_rootedV, map_ofNat]

theorem map_tV (x : A) : ∀ n, φ (tV x n) = tV (φ x) n
  | 0 => by simp [tV]
  | 1 => by simp [tV]
  | n + 2 => by simp [tV, map_tV x (n + 1), map_tV x n, map_ofNat]

theorem map_chInV (wN : ℕ) (x : A) (n Cr : ℕ) : φ (chInV wN x n Cr) = chInV wN (φ x) n Cr := by
  simp [chInV, map_tV]

theorem map_chMidV (wN : ℕ) (x y : A) : ∀ j k2 Cr, φ (chMidV wN x y j k2 Cr) = chMidV wN (φ x) (φ y) j k2 Cr
  | 0, _, _ => by simp [chMidV]
  | j + 1, k2, Cr => by simp [chMidV, map_tV, map_chInV, map_chMidV wN x y j]

theorem map_chOutV (wN : ℕ) (x y z : A) :
    ∀ j k3 Cr, φ (chOutV wN x y z j k3 Cr) = chOutV wN (φ x) (φ y) (φ z) j k3 Cr
  | 0, _, _ => by simp [chOutV]
  | j + 1, k3, Cr => by simp [chOutV, map_tV, map_chMidV, map_chOutV wN x y z j]

end Map

end CAP.Wsos
