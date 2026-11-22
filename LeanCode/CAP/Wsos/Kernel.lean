module

public import CAP.Core.Packed

/-!
# Nonnegativity of a typed three-point form on its domain: the checker (`Init` only)

**State.** The checker is bit-exact with `certgen/wsos.py`. The theorems of soundness are
`CAP.Wsos.checkTy_sound` (`Sound.lean`) for `checkTy` and `CAP.Wsos.gramOk_sound` (`Gram.lean`) for
`gramOk`; the layouts in use are injective (`Layout.lean`).

**Statement.** Let a triple type have the inner products `u, v, t` with `u = (ρ x + c) / 2 ^ m`
for `x ∈ [-1, 1]`, and likewise `v`, `t` with `y`, `z`. The data define a polynomial `Λ` in
`x, y, z`: with the unit `μ₁ μ₂ μ₃ d! 2 ^ (m D)`,

* three shares, one in each of `u`, `v`, `t`: a share is a polynomial with dyadic coefficients,
  or it is given by an equation: `μ` times the share is a polynomial minus multiples of
  polynomials minus the polynomials of two rooted blocks at coinciding points;
* three rooted forms `∑ k, Q k (w₁, w₂, w₃) * ∑ i j, G k ((b, i), (c, j)) * w₁ ^ i * w₂ ^ j` in the
  orders `(u, v, t)`, `(u, t, v)`, `(v, t, u)`, where `Q k` are the kernels with
  `(k + 1) Q (k + 1) = (2 k + 1) (w₃ - w₁ w₂) Q k - k (1 - w₁²) (1 - w₂²) Q (k - 1)`, and `G k` is
  the Gram matrix `Y * Yᵀ` of an integer factor of a rooted block (`gramOk`), so that the block is
  positive semidefinite by its form.

The checker verifies that

  `2 ^ D * (Λ - c - ∑ weights, mul * g * ∑ i, ξ i ^ 2) = ∑ k, N k * T k₁ (x) * T k₂ (y) * T k₃ (z)`

with Chebyshev polynomials `T`, integers `N k` with `∑ k ≠ 0, |N k| ≤ N 0`, weights `g` that are
products of polynomials in `u, v, t` (the generators of the domain), and integer polynomials
`ξ i` of degree at most `delta`. Hence `Λ ≥ c` where the generators are nonnegative.

**Method.** A polynomial in `x, y, z` is the number `P (2 ^ W, 2 ^ (W * k1), 2 ^ (W * k2))` modulo
`2 ^ M`, `M = W * slots`. The map from the monomials of total degree at most `D` to the slots
`a + k1 * b + k2 * c` is injective, and a bound for the coefficients, which the checker computes
from the sizes of the data, excludes carries: the equality of two numbers is the equality of the
polynomials. Sums, products and differences of polynomials are sums, products and differences of
numbers modulo `2 ^ M`.

**Columns.** The polynomials `ξ i` are not data. A weight has a function `col`; the checker takes
the bits of `col i` at the places of the monomials of degree at most `delta` (the mask `allowed`),
which are the coefficients of `ξ i` with the bias `2 ^ (w0 - 1)`. Whatever `col` is, the masked
number is a polynomial of this form. The functions `stage`, `colAt`, `spreadDot`, `spreadGroups2` at the end of the
file are used by the generated files to define `col`; nothing has to be proved about them.
-/

@[expose] public section

namespace CAP.Wsos

/-- Parameters of a certificate. -/
structure Params where
  /-- width of a slot -/
  W : Nat
  /-- the slot of `x ^ a * y ^ b * z ^ c` is `a + k1 * b + k2 * c` -/
  k1 : Nat
  k2 : Nat
  /-- number of slots: `M = W * slots` -/
  slots : Nat
  /-- total degree -/
  D : Nat
  /-- `D = 2 * d` -/
  d : Nat
  /-- `u = (rho * x + cp - cn) / 2 ^ m` -/
  m : Nat
  /-- number of classes -/
  q : Nat
  /-- width of an entry of a factor of a rooted block, bias `2 ^ (rb - 1)`; used by `gramOk` only -/
  rb : Nat
  /-- width of an entry of the Gram matrix of a rooted block, bias `2 ^ (wG - 1)` -/
  wG : Nat
  /-- width of a coefficient of a pair polynomial or of a share, bias `2 ^ (wP - 1)` -/
  wP : Nat
  /-- width of an entry of a column, bias `2 ^ (w0 - 1)` -/
  w0 : Nat
  /-- width of a coefficient of the Chebyshev combination -/
  wN : Nat
  /-- the shares are multiplied by `2 ^ aP` -/
  aP : Nat
  /-- the rooted forms are multiplied by `2 ^ aF` -/
  aF : Nat

/-- The interval of an inner product: `[(cp - cn - rho) / 2 ^ m, (cp - cn + rho) / 2 ^ m]`. -/
structure Box where
  rho : Nat
  cp : Nat
  cn : Nat

/-- The term `(cp - cn) * u ^ e1 * v ^ e2 * t ^ e3` of a generator. -/
structure Term where
  cp : Nat
  cn : Nat
  e1 : Nat
  e2 : Nat
  e3 : Nat

/-- A generator of the domain: a polynomial in `u, v, t` with integer coefficients. -/
structure Gen where
  /-- bound for the degree of its terms -/
  deg : Nat
  terms : List Term

/-- A weight with its squares. -/
structure Weight where
  /-- the weight is the product of these generators -/
  gens : List Gen
  /-- the squared polynomials have degree at most `delta` -/
  delta : Nat
  /-- number of squares -/
  r : Nat
  /-- square `i` is the square of the polynomial that the masked number `col i` holds -/
  col : Nat → Nat
  /-- multiplier -/
  mul : Nat

/-- The rooted blocks of one class in an equation for a share: for every `k` the Gram matrix, the
class of the root and the other class of the pair. -/
structure RootUse where
  gram : List Nat
  self : Nat
  other : Nat

/-- A share: `mult` times the share is the polynomial `pos` minus `negm j` times the polynomial
`negs j` minus the polynomials of the rooted blocks `roots` at coinciding points. -/
structure Share where
  mult : Nat
  pos : Nat
  negs : List Nat
  negm : List Nat
  roots : List RootUse

/-- A rooted form: the Gram matrices of a root for every `k`, and the classes of its two arguments. -/
structure Rooted where
  gram : List Nat
  b : Nat
  c : Nat

/-- The data of a triple type. -/
structure Ty where
  bu : Box
  bv : Box
  bt : Box
  /-- the shares in `u`, `v`, `t` -/
  s1 : Share
  s2 : Share
  s3 : Share
  /-- the rooted forms in the orders `(u, v, t)`, `(u, t, v)`, `(v, t, u)` -/
  r1 : Rooted
  r2 : Rooted
  r3 : Rooted
  weights : List Weight
  /-- the constant `c2p - c2n` -/
  c2p : Nat
  c2n : Nat
  /-- the coefficients `Np k - Nn k` of the Chebyshev combination -/
  Np : Nat
  Nn : Nat

/-! ## Arithmetic modulo `2 ^ M` and lists -/

/-- `a - b` modulo `2 ^ M`, for `pM = 2 ^ M` and `mM = 2 ^ M - 1` -/
def subM (pM mM a b : Nat) : Nat := Nat.sub (Nat.add a pM) (Nat.land b mM)

/-- `a * b` modulo `2 ^ M` -/
def mulM (mM a b : Nat) : Nat := Nat.land (Nat.mul a b) mM

noncomputable def hd : List Nat → Nat := List.rec 0 (fun h _ _ => h)

noncomputable def tl : List Nat → List Nat := List.rec [] (fun _ t _ => t)

noncomputable def lsum : List Nat → Nat := List.rec 0 (fun h _ ih => Nat.add h ih)

noncomputable def len : List Nat → Nat := List.rec 0 (fun _ _ ih => Nat.succ ih)

/-- entry `i` of a list, `0` beyond its end -/
noncomputable def nth : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun h _ ih i => Nat.rec (motive := fun _ => Nat) h (fun j _ => ih j) i)

noncomputable def rep (x : Nat) : Nat → List Nat := Nat.rec [] (fun _ ih => x :: ih)

/-- `[cur, cur * w, cur * w ^ 2, …]` with `n` entries, modulo `2 ^ M` -/
noncomputable def pows (mM w : Nat) : Nat → Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih cur => cur :: ih (mulM mM cur w))

/-- the first `n` entries of `pw`; entry `i` is shifted by `s - m * i` -/
noncomputable def hl (m : Nat) : Nat → List Nat → Nat → List Nat :=
  Nat.rec (motive := fun _ => List Nat → Nat → List Nat) (fun _ _ => [])
    (fun _ ih pw s => Nat.shiftLeft (hd pw) s :: ih (tl pw) (Nat.sub s m))

/-- `U + ∑ j, (slot j of Cr) * b j` for the slots of width `w` of `Cr` and the numbers of a list -/
noncomputable def dot (w mw : Nat) : List Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ U => U)
    (fun b _ ih Cr U => ih (Nat.shiftRight Cr w) (Nat.add U (Nat.mul (Nat.land Cr mw) b)))

/-- `U` plus the sum of the first `n` slots of `Cr` -/
noncomputable def dsum (w mw : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ U => U)
    (fun _ ih Cr U => ih (Nat.shiftRight Cr w) (Nat.add U (Nat.land Cr mw)))

/-- the bias of a polynomial with the powers `h`: `2 ^ (w - 1) * ∑ h` -/
noncomputable def bias (w : Nat) (h : List Nat) : Nat := Nat.shiftLeft (lsum h) (Nat.pred w)

/-- the polynomial `rho * X + cp - cn` -/
def aff (pM mM : Nat) (b : Box) (X : Nat) : Nat :=
  Nat.land (subM pM mM (Nat.add (Nat.mul b.rho X) b.cp) b.cn) mM

noncomputable def factsGo : Nat → Nat → Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → List Nat → List Nat) (fun _ _ acc => acc)
    (fun _ ih k g acc => ih (Nat.pred k) (Nat.mul g k) (Nat.mul g k :: acc))

/-- `[d! / 0!, d! / 1!, …, d! / d!]` -/
noncomputable def facts (d : Nat) : List Nat := factsGo d d 1 [1]

noncomputable def fact : Nat → Nat := Nat.rec 1 (fun k ih => Nat.mul (Nat.succ k) ih)

/-! ## The rooted forms

The rooted block of a root and of `k` is the matrix `G / 4 ^ sF` with an integer matrix `G`, which
`gramOk` shows to be `Y * Yᵀ`. The entry `((b, i), (c, j))` of `G` is the slot
`(b * (n + 1) + i) + N * (c * (n + 1) + j)` of width `wG` of one number, `n = d - k`,
`N = q * (n + 1)`, with the bias `2 ^ (wG - 1)`. -/

/-- `U + ∑ j, h2 j * ∑ i, (slot (i, j) - bias) * h1 i`; row `j` starts at the bit `zN * j` of `Gr` -/
noncomputable def bilGo (wG mG pM mM : Nat) (h1 : List Nat) (b1 zN : Nat) : List Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ U => U)
    (fun hj _ ih Gr U => ih (Nat.shiftRight Gr zN) (Nat.add U (mulM mM hj (subM pM mM (dot wG mG h1 Gr 0) b1))))

noncomputable def bilK (P : Params) (pM mM : Nat) (h1 h2 : List Nat) (zN Gr : Nat) : Nat :=
  bilGo P.wG (mask P.wG) pM mM h1 (bias P.wG h1) zN h2 Gr 0

/-- the bilinear form of the block `(b, c)` of the Gram matrix `G` for `n = d - k`, with the powers `h1`, `h2` -/
noncomputable def bil (P : Params) (pM mM G n b c : Nat) (h1 h2 : List Nat) : Nat :=
  bilK P pM mM h1 h2 (Nat.mul P.wG (Nat.mul P.q (Nat.succ n)))
    (Nat.shiftRight G (Nat.mul P.wG (Nat.add (Nat.mul b (Nat.succ n))
      (Nat.mul (Nat.mul P.q (Nat.succ n)) (Nat.mul c (Nat.succ n))))))

/-- `(2 k + 1) * Ah * cur - k ^ 2 * Wh * prev` modulo `2 ^ M` -/
def qnext (pM mM Ah Wh k prev cur : Nat) : Nat :=
  Nat.land (subM pM mM (Nat.mul (Nat.succ (Nat.mul 2 k)) (mulM mM Ah cur))
    (Nat.mul (Nat.mul k k) (mulM mM Wh prev))) mM

noncomputable def ql (pM mM Ah Wh : Nat) : Nat → Nat → Nat → Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List Nat) (fun _ _ _ => [])
    (fun _ ih k prev cur => cur :: ih (Nat.succ k) cur (qnext pM mM Ah Wh k prev cur))

/-- the kernels `k! * 2 ^ (2 m k) * Q k` for `k ≤ d` at `(w1, w2, w3)` -/
noncomputable def qlist (P : Params) (pM mM w1 w2 w3 : Nat) : List Nat :=
  ql pM mM (Nat.land (subM pM mM (Nat.shiftLeft w3 P.m) (mulM mM w1 w2)) mM)
    (mulM mM (subM pM mM (Nat.shiftLeft 1 (Nat.mul 2 P.m)) (mulM mM w1 w1))
      (subM pM mM (Nat.shiftLeft 1 (Nat.mul 2 P.m)) (mulM mM w2 w2)))
    (Nat.succ P.d) 0 0 1

noncomputable def rootedGo (P : Params) (pM mM : Nat) (pw1 pw2 : List Nat) (b c : Nat) :
    List Nat → List Nat → List Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => List Nat → List Nat → Nat → Nat → Nat) (fun _ _ _ S => S)
    (fun G _ ih qs gs n S =>
      ih (tl qs) (tl gs) (Nat.pred n)
        (Nat.add S (Nat.mul (hd gs) (mulM mM (hd qs)
          (Nat.land (bil P pM mM G n b c (hl P.m (Nat.succ n) pw1 (Nat.mul P.m n))
            (hl P.m (Nat.succ n) pw2 (Nat.mul P.m n))) mM)))))

/-- `∑ k, (d! / k!) * (k! 2 ^ (2 m k) Q k) * ∑ i j, G k ((b, i), (c, j)) * w1 ^ i * w2 ^ j`, homogeneous -/
noncomputable def rootedVal (P : Params) (pM mM : Nat) (R : Rooted) (w1 w2 w3 : Nat) (pw1 pw2 : List Nat) : Nat :=
  rootedGo P pM mM pw1 pw2 R.b R.c R.gram (qlist P pM mM w1 w2 w3) (facts P.d) P.d 0

/-! ## The shares -/

noncomputable def negsGo (wP mP : Nat) (h : List Nat) : List Nat → List Nat → Nat → Nat :=
  List.rec (motive := fun _ => List Nat → Nat → Nat) (fun _ U => U)
    (fun c _ ih ms U => ih (tl ms) (Nat.add U (Nat.mul (hd ms) (dot wP mP h c 0))))

/-- `U + ∑ j, (sum of the `cnt` slots of row `j`) * h j` -/
noncomputable def linGo (wG mG cnt zN : Nat) : List Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ U => U)
    (fun hj _ ih Gr U => ih (Nat.shiftRight Gr zN) (Nat.add U (Nat.mul (dsum wG mG cnt Gr 0) hj)))

/-- `∑ i j, G₀ ((self, i), (other, j)) * w ^ j` -/
noncomputable def firstK (P : Params) (pM mM : Nat) (h : List Nat) (Gr : Nat) : Nat :=
  subM pM mM (linGo P.wG (mask P.wG) (Nat.succ P.d) (Nat.mul P.wG (Nat.mul P.q (Nat.succ P.d))) h Gr 0)
    (Nat.mul (Nat.shiftLeft (Nat.succ P.d) (Nat.pred P.wG)) (lsum h))

noncomputable def dStep (P : Params) (pM mM G n b : Nat) (h : List Nat) : Nat := bil P pM mM G n b b h h

noncomputable def dGo (P : Params) (pM mM : Nat) (pw : List Nat) (Vh b : Nat) : List Nat → Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ S => S)
    (fun G _ ih vk n S =>
      ih (mulM mM vk Vh) (Nat.pred n)
        (Nat.add S (mulM mM vk (Nat.land (dStep P pM mM G n b (hl P.m (Nat.succ n) pw (Nat.mul P.m n))) mM))))

/-- the polynomial of the rooted blocks of a class at coinciding points:
`2 * 2 ^ (m d) * ∑ i j, G₀ ((self, i), (other, j)) * w ^ j
  + ∑ k, (2 ^ (2 m) - w ^ 2) ^ k * ∑ i j, G k ((other, i), (other, j)) * w ^ (i + j)`, homogeneous -/
noncomputable def rootUseVal (P : Params) (pM mM w : Nat) (pw : List Nat) (Ru : RootUse) : Nat :=
  Nat.add
    (Nat.shiftLeft (Nat.land (firstK P pM mM (hl P.m (Nat.succ P.d) pw (Nat.mul P.m P.d))
        (Nat.shiftRight (hd Ru.gram) (Nat.mul P.wG (Nat.add (Nat.mul Ru.self (Nat.succ P.d))
          (Nat.mul (Nat.mul P.q (Nat.succ P.d)) (Nat.mul Ru.other (Nat.succ P.d))))))) mM)
      (Nat.succ (Nat.mul P.m P.d)))
    (dGo P pM mM pw (Nat.land (subM pM mM (Nat.shiftLeft 1 (Nat.mul 2 P.m)) (mulM mM w w)) mM) Ru.other Ru.gram 1 P.d 0)

noncomputable def rootsGo (P : Params) (pM mM w : Nat) (pw : List Nat) : List RootUse → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun U => U)
    (fun Ru _ ih U => ih (Nat.add U (Nat.land (rootUseVal P pM mM w pw Ru) mM)))

noncomputable def shareK (P : Params) (pM mM fd : Nat) (S : Share) (h : List Nat) (bh rootsV : Nat) : Nat :=
  Nat.land (subM pM mM
    (Nat.shiftLeft (Nat.mul fd (Nat.add (dot P.wP (mask P.wP) h S.pos 0) (Nat.mul (lsum S.negm) bh))) P.aP)
    (Nat.add (Nat.shiftLeft (Nat.mul fd (negsGo P.wP (mask P.wP) h S.negs S.negm bh)) P.aP)
      (Nat.shiftLeft (Nat.mul fd rootsV) P.aF))) mM

noncomputable def shareH (P : Params) (pM mM fd : Nat) (S : Share) (h : List Nat) (rootsV : Nat) : Nat :=
  shareK P pM mM fd S h (bias P.wP h) rootsV

/-- `mult * d! * 2 ^ (m D)` times the share, in the unit of the form -/
noncomputable def shareVal (P : Params) (pM mM fd : Nat) (S : Share) (w : Nat) (pw : List Nat) : Nat :=
  shareH P pM mM fd S (hl P.m (Nat.succ P.D) pw (Nat.mul P.m P.D)) (rootsGo P pM mM w pw S.roots 0)

/-! ## The weights -/

noncomputable def powM (mM w : Nat) : Nat → Nat := Nat.rec 1 (fun _ ih => mulM mM ih w)

noncomputable def genGo (P : Params) (pM mM u v t deg : Nat) : List Term → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun Pp Nn => Nat.land (subM pM mM Pp Nn) mM)
    (fun tm _ ih Pp Nn =>
      (fun mon => ih (Nat.add Pp (Nat.mul tm.cp mon)) (Nat.add Nn (Nat.mul tm.cn mon)))
        (Nat.shiftLeft (mulM mM (mulM mM (powM mM u tm.e1) (powM mM v tm.e2)) (powM mM t tm.e3))
          (Nat.mul P.m (Nat.sub deg (Nat.add (Nat.add tm.e1 tm.e2) tm.e3)))))

/-- `acc` times the generators at `(u, v, t)`, each multiplied by `2 ^ (m * deg)` -/
noncomputable def gensGo (P : Params) (pM mM u v t : Nat) : List Gen → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun g _ ih acc => ih (mulM mM acc (genGo P pM mM u v t g.deg g.terms 0 0)))

/-- the numbers of `∑ a + b + c ≤ δ, x ^ a * y ^ b * z ^ c` for `δ = 0, 1, …` -/
noncomputable def monoGo (sX sY sZ : Nat) : Nat → Nat → Nat → Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List Nat) (fun _ _ _ => [])
    (fun _ ih m1 m2 m3 => m3 ::
      (fun a => (fun b => ih a b (Nat.add b (Nat.shiftLeft m3 sZ))) (Nat.add a (Nat.shiftLeft m2 sY)))
        (Nat.succ (Nat.shiftLeft m1 sX)))

/-- `|a - b|` -/
def absd (a b : Nat) : Nat := Nat.add (Nat.sub a b) (Nat.sub b a)

/-- `(e - beta) ^ 2` -/
def sqAbs (e beta : Nat) : Nat := (fun a => Nat.mul a a) (absd e beta)

/-- `∑ i < r, ξ i ^ 2`, where `ξ i` has the coefficients `(slot of col i) - 2 ^ (w0 - 1)` at the
monomials of `allowed`; `beta` is the number of the polynomial with all coefficients `2 ^ (w0 - 1)` -/
noncomputable def sqSum (allowed beta : Nat) (col : Nat → Nat) : Nat → Nat :=
  Nat.rec 0 (fun i ih => Nat.add ih (sqAbs (Nat.land (col i) allowed) beta))

noncomputable def weightVal (P : Params) (pM mM u v t mono : Nat) (w : Weight) : Nat :=
  Nat.mul w.mul (mulM mM (gensGo P pM mM u v t w.gens 1)
    (sqSum (Nat.mul (mask P.w0) mono) (Nat.shiftLeft mono (Nat.pred P.w0)) w.col w.r))

noncomputable def weightsGo (P : Params) (pM mM u v t : Nat) (monos : List Nat) : List Weight → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun w _ ih acc => ih (Nat.add acc (weightVal P pM mM u v t (nth monos w.delta) w)))

/-! ## The Chebyshev combination -/

/-- `[prev, cur, 2 X cur - prev, …]` with `n` entries; `s` is one more than the bit of `X` -/
noncomputable def chl (pM mM s : Nat) : Nat → Nat → Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → List Nat) (fun _ _ => [])
    (fun _ ih prev cur => prev :: ih cur (Nat.land (subM pM mM (Nat.shiftLeft cur s) prev) mM))

noncomputable def dotC (w mw : Nat) : Nat → List Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => List Nat → Nat → Nat → Nat) (fun _ _ U => U)
    (fun _ ih ts Cr U => ih (tl ts) (Nat.shiftRight Cr w) (Nat.add U (Nat.mul (Nat.land Cr mw) (hd ts))))

noncomputable def chMid (w mw mM : Nat) (tx : List Nat) : Nat → List Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => List Nat → Nat → Nat → Nat) (fun _ _ U => U)
    (fun j ih ty Cr U => ih (tl ty) (Nat.shiftRight Cr (Nat.mul w (Nat.succ j)))
      (Nat.add U (mulM mM (hd ty) (dotC w mw (Nat.succ j) tx Cr 0))))

/-- `U + ∑ k₁ + k₂ + k₃ < n, (slot of Cr) * tx k₁ * ty k₂ * tz k₃`; the slots are ordered by `k₃`,
then `k₂`, then `k₁` -/
noncomputable def chOut (w mw mM : Nat) (tx ty : List Nat) : Nat → List Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => List Nat → Nat → Nat → Nat) (fun _ _ U => U)
    (fun j ih tz Cr U =>
      ih (tl tz) (Nat.shiftRight Cr (Nat.mul w (Nat.div (Nat.mul (Nat.succ j) (Nat.succ (Nat.succ j))) 2)))
        (Nat.add U (mulM mM (hd tz) (chMid w mw mM tx (Nat.succ j) ty Cr 0))))

noncomputable def chebVal (P : Params) (pM mM N : Nat) : Nat :=
  chOut P.wN (mask P.wN) mM
    (chl pM mM (Nat.succ P.W) (Nat.succ P.D) 1 (Nat.shiftLeft 1 P.W))
    (chl pM mM (Nat.succ (Nat.mul P.W P.k1)) (Nat.succ P.D) 1 (Nat.shiftLeft 1 (Nat.mul P.W P.k1)))
    (Nat.succ P.D)
    (chl pM mM (Nat.succ (Nat.mul P.W P.k2)) (Nat.succ P.D) 1 (Nat.shiftLeft 1 (Nat.mul P.W P.k2)))
    N 0

/-- the number of monomials of degree at most `δ` in three variables -/
def nmon (δ : Nat) : Nat := Nat.div (Nat.mul (Nat.mul (Nat.succ δ) (Nat.add δ 2)) (Nat.add δ 3)) 6

/-- the sum of the coefficients of a Chebyshev combination -/
noncomputable def chebSum (P : Params) (N : Nat) : Nat := dsum P.wN (mask P.wN) (nmon P.D) N 0

/-! ## The bound for the coefficients -/

noncomputable def rhoL : Nat → Nat → Nat → Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List Nat) (fun _ _ _ => [])
    (fun _ ih k prev cur => cur :: ih (Nat.succ k) cur
      (Nat.add (Nat.mul (Nat.succ (Nat.mul 2 k)) cur) (Nat.mul (Nat.mul k k) prev)))

/-- `acc + ∑ k, fs k * 2 ^ k * (n k + 1) ^ 2` with `n k = d - k` -/
noncomputable def kSum : List Nat → Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun f _ ih n k acc => ih (Nat.pred n) (Nat.succ k)
      (Nat.add acc (Nat.mul (Nat.mul f (Nat.shiftLeft 1 k)) (Nat.mul (Nat.succ n) (Nat.succ n)))))

noncomputable def nRootUse (P : Params) : Nat :=
  Nat.add (Nat.mul 2 (Nat.mul (Nat.succ P.d) (Nat.succ P.d))) (kSum (rep 1 (Nat.succ P.d)) P.d 0 0)

noncomputable def lenR : List RootUse → Nat := List.rec 0 (fun _ _ ih => Nat.succ ih)

noncomputable def nShare (P : Params) (S : Share) : Nat :=
  Nat.shiftLeft
    (Nat.add (Nat.shiftLeft (Nat.mul (Nat.succ (lsum S.negm)) (Nat.succ P.D)) (Nat.add (Nat.pred P.wP) P.aP))
      (Nat.shiftLeft (Nat.mul (lenR S.roots) (nRootUse P)) (Nat.add (Nat.pred P.wG) P.aF)))
    (Nat.mul P.m P.D)

noncomputable def zipMul : List Nat → List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun a _ ih bs => Nat.mul a (hd bs) :: ih (tl bs))

noncomputable def nRooted (P : Params) : Nat :=
  Nat.shiftLeft (kSum (zipMul (facts P.d) (rhoL (Nat.succ P.d) 0 0 1)) P.d 0 0)
    (Nat.add (Nat.pred P.wG) (Nat.mul P.m P.D))

noncomputable def termSum : List Term → Nat := List.rec 0 (fun tm _ ih => Nat.add (Nat.add tm.cp tm.cn) ih)

noncomputable def nGen (P : Params) (g : Gen) : Nat := Nat.shiftLeft (termSum g.terms) (Nat.mul P.m g.deg)

noncomputable def nGens (P : Params) : List Gen → Nat := List.rec 1 (fun g _ ih => Nat.mul (nGen P g) ih)

noncomputable def nWeightsGo (P : Params) : List Weight → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun w _ ih acc => ih (Nat.add acc (Nat.mul (Nat.mul (Nat.mul w.mul (nGens P w.gens)) w.r)
      (Nat.shiftLeft (Nat.mul (nmon w.delta) (nmon w.delta)) (Nat.sub (Nat.mul 2 P.w0) 2)))))

/-- A bound for the sum of the absolute values of the coefficients of `2 ^ D` times the residual
and of the Chebyshev combination; `sp`, `sn` are the sums of the coefficients `Np`, `Nn`. -/
noncomputable def bound (P : Params) (T : Ty) (sp sn : Nat) : Nat :=
  Nat.add
    (Nat.shiftLeft
      (Nat.add (Nat.add (Nat.add
        (Nat.add
          (Nat.mul (fact P.d) (Nat.add (Nat.add (Nat.mul (Nat.mul T.s2.mult T.s3.mult) (nShare P T.s1))
            (Nat.mul (Nat.mul T.s1.mult T.s3.mult) (nShare P T.s2))) (Nat.mul (Nat.mul T.s1.mult T.s2.mult) (nShare P T.s3))))
          (Nat.shiftLeft (Nat.mul (Nat.mul 2 (Nat.mul (Nat.mul T.s1.mult T.s2.mult) T.s3.mult))
            (Nat.mul 3 (nRooted P))) P.aF))
        T.c2p) T.c2n) (nWeightsGo P T.weights 0))
      P.D)
    (Nat.mul (Nat.add sp sn) (Nat.pow 3 P.D))

/-! ## The conditions on the sizes -/

def boxOk (P : Params) (b : Box) : Bool :=
  Nat.ble 1 b.rho && Nat.ble (Nat.add (Nat.add b.rho b.cp) b.cn) (Nat.shiftLeft 1 P.m)

noncomputable def termsOk (deg : Nat) : List Term → Bool :=
  List.rec true (fun tm _ ih => Nat.ble (Nat.add (Nat.add tm.e1 tm.e2) tm.e3) deg && ih)

noncomputable def gensOk : List Gen → Bool := List.rec true (fun g _ ih => termsOk g.deg g.terms && ih)

noncomputable def degSum : List Gen → Nat := List.rec 0 (fun g _ ih => Nat.add g.deg ih)

noncomputable def weightOk (P : Params) (w : Weight) : Bool :=
  gensOk w.gens && Nat.ble (Nat.add (degSum w.gens) (Nat.mul 2 w.delta)) P.D

noncomputable def weightsOk (P : Params) : List Weight → Bool := List.rec true (fun w _ ih => weightOk P w && ih)

def paramsOk (P : Params) : Bool :=
  Nat.ble 1 P.k1 && Nat.ble P.k1 P.k2 && Nat.blt (Nat.mul P.k2 P.D) P.slots && Nat.beq P.D (Nat.mul 2 P.d)
    && Nat.ble 1 P.wG && Nat.ble 1 P.wP && Nat.ble 1 P.w0 && Nat.ble P.w0 P.W

noncomputable def rootsOk (P : Params) : List RootUse → Bool :=
  List.rec true (fun Ru _ ih => Nat.ble (len Ru.gram) (Nat.succ P.d) && ih)

noncomputable def shareOk (P : Params) (S : Share) : Bool :=
  Nat.ble 1 S.mult && Nat.beq (len S.negs) (len S.negm) && rootsOk P S.roots

noncomputable def flags (P : Params) (T : Ty) : Bool :=
  paramsOk P && boxOk P T.bu && boxOk P T.bv && boxOk P T.bt && shareOk P T.s1 && shareOk P T.s2
    && shareOk P T.s3 && Nat.ble (len T.r1.gram) (Nat.succ P.d) && Nat.ble (len T.r2.gram) (Nat.succ P.d)
    && Nat.ble (len T.r3.gram) (Nat.succ P.d) && weightsOk P T.weights

/-! ## The checker -/

noncomputable def residualK (P : Params) (T : Ty) (pM mM u v t : Nat) (pu pv pt : List Nat) : Nat :=
  subM pM mM
    (Nat.add (Nat.add (Nat.add
      (Nat.mul (Nat.mul T.s2.mult T.s3.mult) (shareVal P pM mM (fact P.d) T.s1 u pu))
      (Nat.mul (Nat.mul T.s1.mult T.s3.mult) (shareVal P pM mM (fact P.d) T.s2 v pv)))
      (Nat.mul (Nat.mul T.s1.mult T.s2.mult) (shareVal P pM mM (fact P.d) T.s3 t pt))) T.c2n)
    (Nat.add (Nat.add
      (Nat.shiftLeft (Nat.mul (Nat.mul 2 (Nat.mul (Nat.mul T.s1.mult T.s2.mult) T.s3.mult))
        (Nat.land (Nat.add (Nat.add (rootedVal P pM mM T.r1 u v t pu pv) (rootedVal P pM mM T.r2 u t v pu pt))
          (rootedVal P pM mM T.r3 v t u pv pt)) mM)) P.aF)
      T.c2p)
      (weightsGo P pM mM u v t (monoGo P.W (Nat.mul P.W P.k1) (Nat.mul P.W P.k2) (Nat.succ P.d) 1 1 1) T.weights 0))

noncomputable def residualU (P : Params) (T : Ty) (pM mM u v t : Nat) : Nat :=
  residualK P T pM mM u v t (pows mM u (Nat.succ P.D) 1) (pows mM v (Nat.succ P.D) 1) (pows mM t (Nat.succ P.D) 1)

/-- The number of the residual `Λ - c - ∑ weights` modulo `2 ^ M`. -/
noncomputable def residual (P : Params) (T : Ty) (pM mM : Nat) : Nat :=
  residualU P T pM mM (aff pM mM T.bu (Nat.shiftLeft 1 P.W)) (aff pM mM T.bv (Nat.shiftLeft 1 (Nat.mul P.W P.k1)))
    (aff pM mM T.bt (Nat.shiftLeft 1 (Nat.mul P.W P.k2)))

noncomputable def checkK (P : Params) (T : Ty) (pM mM sp sn : Nat) : Bool :=
  flags P T && Nat.blt (bound P T sp sn) (Nat.shiftLeft 1 (Nat.pred P.W))
    && Nat.beq (Nat.land (Nat.shiftLeft (residual P T pM mM) P.D) mM)
        (Nat.land (subM pM mM (chebVal P pM mM T.Np) (chebVal P pM mM T.Nn)) mM)
    && Nat.ble (Nat.add sp sn) (Nat.mul 2 (Nat.land T.Np (mask P.wN)))

/-- The checker of a triple type. -/
noncomputable def checkTy (P : Params) (T : Ty) : Bool :=
  (fun pM => checkK P T pM (Nat.sub pM 1) (chebSum P T.Np) (chebSum P T.Nn)) (Nat.shiftLeft 1 (Nat.mul P.W P.slots))

/-! ## The Gram matrices of the rooted blocks -/

/-- The product `(A - bA) * (Bv - bB)` modulo `2 ^ Mg`, where `A` and `Bv` hold the `n` entries of
the column `c` at the strides `z` and `zN`. -/
noncomputable def vecGo (rb mr z zN mMg pMg bA bB : Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat)
    (fun _ A Bv _ _ => mulM mMg (subM pMg mMg A bA) (subM pMg mMg Bv bB))
    (fun _ ih c A Bv sa sb =>
      ih (Nat.shiftRight c rb) (Nat.add A (Nat.shiftLeft (Nat.land c mr) sa))
        (Nat.add Bv (Nat.shiftLeft (Nat.land c mr) sb)) (Nat.add sa z) (Nat.add sb zN))

noncomputable def gramGo (rb mr z zN mMg pMg bA bB N : Nat) : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun c _ ih S => ih (Nat.add S (vecGo rb mr z zN mMg pMg bA bB N c 0 0 0 0)))

noncomputable def gramK (P : Params) (N z zN pMg mMg : Nat) (cols : List Nat) (G : Nat) : Bool :=
  Nat.ble 1 P.rb && Nat.ble 1 z && Nat.blt G pMg
    && Nat.blt (Nat.shiftLeft (len cols) (Nat.sub (Nat.mul 2 P.rb) 2)) (Nat.shiftLeft 1 (Nat.pred z))
    && Nat.beq (Nat.land (gramGo P.rb (mask P.rb) z zN mMg pMg (Nat.shiftLeft (ones z N) (Nat.pred P.rb))
          (Nat.shiftLeft (ones zN N) (Nat.pred P.rb)) N cols 0) mMg)
        (Nat.land (subM pMg mMg G (Nat.shiftLeft (ones z (Nat.mul N N)) (Nat.pred z))) mMg)

/-- The number `G` holds the matrix `∑ columns, y * yᵀ` for the columns `y` of `cols`, which have
`N = q * (n + 1)` entries of width `rb` with the bias `2 ^ (rb - 1)`: the entry `(p, p')` is the slot
`p + N * p'` of width `wG` of `G`, with the bias `2 ^ (wG - 1)`. -/
noncomputable def gramOk (P : Params) (n : Nat) (cols : List Nat) (G : Nat) : Bool :=
  (fun N => (fun zN => (fun pMg => gramK P N P.wG zN pMg (Nat.sub pMg 1) cols G) (Nat.shiftLeft 1 (Nat.mul zN N)))
    (Nat.mul P.wG N)) (Nat.mul P.q (Nat.succ n))

/-! ## Functions for the columns (not trusted) -/

/-- The bits of `x` in the mask `mv` move up by `sh`. -/
def stage (mv sh x : Nat) : Nat := (fun t => Nat.add (Nat.sub x t) (Nat.shiftLeft t sh)) (Nat.land x mv)

/-- Column `i` of an upper triangular factor whose columns are stored one after the other in `cd`
(column `i` has `i + 1` entries of width `w0`), followed by the entries of `Bn` above them. -/
def colAt (w0 Bn cd i : Nat) : Nat :=
  (fun wi => Nat.add (Nat.land (Nat.shiftRight cd (Nat.mul w0 (Nat.div (Nat.mul i (Nat.succ i)) 2))) (mask wi))
      (Nat.sub Bn (Nat.land Bn (mask wi))))
    (Nat.mul w0 (Nat.succ i))

/-- Entry `j` of width `w0` of `x` is moved to the bit `ps j`. -/
noncomputable def spreadDot (w0 m0 : Nat) : List Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ U => U)
    (fun p _ ih x U => ih (Nat.shiftRight x w0) (Nat.add U (Nat.shiftLeft (Nat.land x m0) p)))

/-- The number of the entries of a list of groups. -/
noncomputable def lenG : List (Nat × List Nat) → Nat := List.rec 0 (fun g _ ih => Nat.add (len g.2) ih)

/-- The entries of width `w0` of `x` are moved group by group: a group `(p, qs)` takes the next entries of `x`,
moves them to the bits `qs` of a small number, and this number to the bit `p`. The large number is touched once for
every group, not once for every entry. -/
noncomputable def spreadGroups (w0 m0 : Nat) : List (Nat × List Nat) → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ U => U)
    (fun g _ ih x U =>
      ih (Nat.shiftRight x (Nat.mul w0 (len g.2))) (Nat.add U (Nat.shiftLeft (spreadDot w0 m0 g.2 x 0) g.1)))

/-- The same with two levels of groups: a group `(p, gs)` moves the number of its groups `gs` to the bit `p`. -/
noncomputable def spreadGroups2 (w0 m0 : Nat) : List (Nat × List (Nat × List Nat)) → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ U => U)
    (fun g _ ih x U =>
      ih (Nat.shiftRight x (Nat.mul w0 (lenG g.2))) (Nat.add U (Nat.shiftLeft (spreadGroups w0 m0 g.2 x 0) g.1)))

end CAP.Wsos
