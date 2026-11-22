module

public import CAP.Wsos.Cert
public import CAP.UniPos.PolyKernel

/-!
# A typed certificate as a whole: the checks on its bound, its domain and its sign conditions (`Init` only)

The theorem of the schema (`CAP.Wsos.typed_bound`) bounds the sum of the pair polynomials over the
pairs of points from below, in the unit of the checker and for points in the domain of the checker.
Three checks turn it into a bound for the energy `∑ 1 / (2 - 2 t)` on the domain that the source
declares. Each of them is bit-exact with `certgen/wsos.py`.

**The bound** (`boundOk`). Let `cnt a b c` be the number of triples of distinct points with the
classes `a`, `b`, `c`, let `c2 / (d! μ)` be the constant of a triple type with the product `μ` of the
multiplicities of its shares, and let `g a` be the sum of the entries of the block `(a, a)` of the
Gram matrix of degree `0` of the class `a` (the rooted form of the class at three coinciding points
is `2 ^ (aF + 2 m d) g a`). With a common multiple `M` of the numbers `μ`, the check is

  `6 d! M 2 ^ (m D + aP + sP) tp + tq (Sn + R Gp) < tq (Sp + R Gn)`,   `R = 6 d! M 2 ^ (aF + 2 m d)`,

where `Sp - Sn = ∑ cnt c2 (M / μ)` over all triples of classes and `Gp - Gn = ∑ n a * g a`. It
states that the bound of the certificate exceeds `tp / tq`. The number `sP` is the scale of the pair
polynomials: the sign conditions are stated with it.

**The domain** (`domOk`). The source gives an interval for every pair type (`Ival`) and further
inequalities for a triple type (`Cuts`). The check verifies that the box of the checker contains the
interval, and that every generator of every weight is one of: the six generators of the end points of
the three intervals (`loGen`, `hiGen`), the Gram determinant (`detGen`), one of the six inequalities
of Cauchy and Schwarz for the sum or the difference of two points and the third one (`csGenU`, …,
`csGenTm`), or a cut of the list.

**The sign conditions** (`signOk`). For a pair type with the pair polynomial `Hs / 2 ^ sP` the witness
is an instance of `CAP.UniPos.checkPoly` for the polynomial `den ^ n (2 ^ sP - (2 - 2 t) Hs (t))`,
`n = D + 1`, in the variable `y = den t`. The check compares the coefficients of the witness with the
digits of the pair polynomial (`linkAt`) and its interval with the interval of the pair type.

**The claims** (`claimOk`). A claim of the source gives an interval `K` for every pair type; all of them
lie below the separation bound `T`. A pair type `ω` with exactly one pair of points (one class of two
points, or two classes of one point) is a one-edge type, and the two points of its pair are partners.
The check verifies the conditions (D1) and (D2) of the source: every interval of the domain contains the
interval of the claim, where its lower end may also be a cap bound through a partner, with a rational
witness (`capIneq`); and every cut of the domain is a support polynomial `κ (u + v) + B t + G`, or one
of its two permutations, whose root has a partner outside the triple and whose constant satisfies the
inequality of the support bound with a rational witness (`supIneq`). Then every configuration of the
claim lies in the domain, without hypotheses on the cuts.
-/

@[expose] public section

namespace CAP.Wsos

/-! ## Loops over classes -/

/-- `∑ x < n, f x` -/
noncomputable def sumN (f : Nat → Nat) : Nat → Nat := Nat.rec 0 (fun k ih => Nat.add ih (f k))

/-- `f x` for all `x < n` -/
noncomputable def allN (f : Nat → Bool) : Nat → Bool := Nat.rec true (fun k ih => ih && f k)

noncomputable def sum3N (f : Nat → Nat → Nat → Nat) (q : Nat) : Nat :=
  sumN (fun a => sumN (fun b => sumN (fun c => f a b c) q) q) q

noncomputable def all2N (f : Nat → Nat → Bool) (q : Nat) : Bool := allN (fun a => allN (fun b => f a b) q) q

noncomputable def all3N (f : Nat → Nat → Nat → Bool) (q : Nat) : Bool :=
  allN (fun a => allN (fun b => allN (fun c => f a b c) q) q) q

noncomputable def allX (f : TyX → Bool) : List TyX → Bool := List.rec true (fun X _ ih => f X && ih)

/-! ## The bound -/

/-- The term of the triple of classes `(a, b, c)` in the sum of the constants, multiplied by `d! * M`:
`cnt * c * (M / μ)` for the part `c = sel X` of the constant of its triple type `X`. -/
noncomputable def cTerm (C : Cert) (xs : List TyX) (M : Nat) (sel : TyX → Nat) (a b c : Nat) : Nat :=
  (fun X => Nat.mul (Nat.mul (cnt C a b c) (sel X)) (Nat.div M (tmult C X))) (typeOf xs a b c)

/-- If the triple of classes occurs, then the product of the multiplicities of its triple type divides `M`. -/
noncomputable def divOk (C : Cert) (xs : List TyX) (M a b c : Nat) : Bool :=
  Nat.beq (cnt C a b c) 0 || Nat.beq (Nat.mod M (tmult C (typeOf xs a b c))) 0

/-- The sum of the slots of the block `(a, a)` of the Gram matrix of degree `0` of the class `a`. -/
noncomputable def rootDiag (P : Params) (C : Cert) (a : Nat) : Nat :=
  linGo P.wG (mask P.wG) (Nat.succ P.d) (Nat.mul P.wG (Nat.mul P.q (Nat.succ P.d))) (rep 1 (Nat.succ P.d))
    (Nat.shiftRight (hd (C.gram a)) (Nat.mul P.wG (Nat.add (Nat.mul a (Nat.succ P.d))
      (Nat.mul (Nat.mul P.q (Nat.succ P.d)) (Nat.mul a (Nat.succ P.d)))))) 0

/-- The sum of the biases of the entries of such a block: `(d + 1) ^ 2 * 2 ^ (wG - 1)`. -/
def rootNeg (P : Params) : Nat := Nat.shiftLeft (Nat.mul (Nat.succ P.d) (Nat.succ P.d)) (Nat.pred P.wG)

/-- `6 * d! * M` -/
noncomputable def bF (P : Params) (M : Nat) : Nat := Nat.mul (Nat.mul 6 (fact P.d)) M

/-- `6 * d! * M * 2 ^ (aF + 2 m d)` -/
noncomputable def bR (P : Params) (M : Nat) : Nat :=
  Nat.mul (bF P M) (Nat.shiftLeft 1 (Nat.add P.aF (Nat.mul (Nat.mul 2 P.m) P.d)))

/-- The bound of the certificate exceeds `tp / tq`. -/
noncomputable def boundOk (P : Params) (C : Cert) (xs : List TyX) (sP M tp tq : Nat) : Bool :=
  Nat.ble 1 M && Nat.ble 1 tq && all3N (divOk C xs M) P.q
    && Nat.blt
      (Nat.add (Nat.mul (Nat.mul (bF P M) (Nat.shiftLeft 1 (Nat.add (Nat.add (Nat.mul P.m P.D) P.aP) sP))) tp)
        (Nat.mul tq (Nat.add (sum3N (cTerm C xs M fun X => X.c2n) P.q)
          (Nat.mul (bR P M) (sumN (fun a => Nat.mul (C.n a) (rootDiag P C a)) P.q)))))
      (Nat.mul tq (Nat.add (sum3N (cTerm C xs M fun X => X.c2p) P.q)
        (Nat.mul (bR P M) (sumN (fun a => Nat.mul (C.n a) (rootNeg P)) P.q))))

/-! ## The domain -/

/-- A rational interval `[(lp - ln) / ld, (hp - hn) / hd]`. -/
structure Ival where
  lp : Nat
  ln : Nat
  ld : Nat
  hp : Nat
  hn : Nat
  hd : Nat

/-- The further inequalities of the triple type `a ≤ b ≤ c`: polynomials in the three inner products that
are nonnegative on the domain. -/
structure Cuts where
  a : Nat
  b : Nat
  c : Nat
  gens : List Gen

/-- The domain of a typed certificate as the source declares it. -/
structure Dom where
  /-- the interval of the inner products of a pair type `a ≤ b` -/
  iv : Nat → Nat → Ival
  /-- the further inequalities of the triple types -/
  cuts : List Cuts

/-- `ld * w - (lp - ln)` for the variable `w = u ^ e1 * v ^ e2 * t ^ e3` (one exponent is `1`). -/
def loGen (I : Ival) (e1 e2 e3 : Nat) : Gen := ⟨1, [⟨I.ln, I.lp, 0, 0, 0⟩, ⟨I.ld, 0, e1, e2, e3⟩]⟩

/-- `(hp - hn) - hd * w` -/
def hiGen (I : Ival) (e1 e2 e3 : Nat) : Gen := ⟨1, [⟨I.hp, I.hn, 0, 0, 0⟩, ⟨0, I.hd, e1, e2, e3⟩]⟩

/-- The Gram determinant of three unit vectors: `1 - t ^ 2 - v ^ 2 + 2 u v t - u ^ 2`. -/
def detGen : Gen := ⟨3, [⟨1, 0, 0, 0, 0⟩, ⟨0, 1, 0, 0, 2⟩, ⟨0, 1, 0, 2, 0⟩, ⟨2, 0, 1, 1, 1⟩, ⟨0, 1, 2, 0, 0⟩]⟩

/-- `2 + 2 u - (v + t) ^ 2` -/
def csGenU : Gen := ⟨2, [⟨2, 0, 0, 0, 0⟩, ⟨0, 1, 0, 0, 2⟩, ⟨0, 2, 0, 1, 1⟩, ⟨0, 1, 0, 2, 0⟩, ⟨2, 0, 1, 0, 0⟩]⟩

/-- `2 + 2 v - (u + t) ^ 2` -/
def csGenV : Gen := ⟨2, [⟨2, 0, 0, 0, 0⟩, ⟨0, 1, 0, 0, 2⟩, ⟨2, 0, 0, 1, 0⟩, ⟨0, 2, 1, 0, 1⟩, ⟨0, 1, 2, 0, 0⟩]⟩

/-- `2 + 2 t - (u + v) ^ 2` -/
def csGenT : Gen := ⟨2, [⟨2, 0, 0, 0, 0⟩, ⟨2, 0, 0, 0, 1⟩, ⟨0, 1, 0, 2, 0⟩, ⟨0, 2, 1, 1, 0⟩, ⟨0, 1, 2, 0, 0⟩]⟩

/-- `2 - 2 u - (v - t) ^ 2` -/
def csGenUm : Gen := ⟨2, [⟨2, 0, 0, 0, 0⟩, ⟨0, 1, 0, 0, 2⟩, ⟨2, 0, 0, 1, 1⟩, ⟨0, 1, 0, 2, 0⟩, ⟨0, 2, 1, 0, 0⟩]⟩

/-- `2 - 2 v - (u - t) ^ 2` -/
def csGenVm : Gen := ⟨2, [⟨2, 0, 0, 0, 0⟩, ⟨0, 1, 0, 0, 2⟩, ⟨0, 2, 0, 1, 0⟩, ⟨2, 0, 1, 0, 1⟩, ⟨0, 1, 2, 0, 0⟩]⟩

/-- `2 - 2 t - (u - v) ^ 2` -/
def csGenTm : Gen := ⟨2, [⟨2, 0, 0, 0, 0⟩, ⟨0, 2, 0, 0, 1⟩, ⟨0, 1, 0, 2, 0⟩, ⟨2, 0, 1, 1, 0⟩, ⟨0, 1, 2, 0, 0⟩]⟩

def termBeq (s t : Term) : Bool :=
  Nat.beq s.cp t.cp && Nat.beq s.cn t.cn && Nat.beq s.e1 t.e1 && Nat.beq s.e2 t.e2 && Nat.beq s.e3 t.e3

noncomputable def termsBeq : List Term → List Term → Bool :=
  List.rec (motive := fun _ => List Term → Bool) (fun l => List.rec true (fun _ _ _ => false) l)
    (fun s _ ih l => List.rec false (fun t tl _ => termBeq s t && ih tl) l)

/-- The two generators are the same data. -/
noncomputable def genBeq (g k : Gen) : Bool := Nat.beq g.deg k.deg && termsBeq g.terms k.terms

noncomputable def genMem (g : Gen) : List Gen → Bool := List.rec false (fun k _ ih => genBeq g k || ih)

noncomputable def gensIn (allowed : List Gen) : List Gen → Bool := List.rec true (fun g _ ih => genMem g allowed && ih)

/-- Every generator of every weight is in the list `allowed`. -/
noncomputable def weightsIn (allowed : List Gen) : List Weight → Bool :=
  List.rec true (fun w _ ih => gensIn allowed w.gens && ih)

/-- The cuts of the triple type `(a, b, c)`. -/
noncomputable def findCuts (a b c : Nat) : List Cuts → List Gen :=
  List.rec [] (fun X _ ih => cond (Nat.beq X.a a && Nat.beq X.b b && Nat.beq X.c c) X.gens ih)

/-- The generators that are nonnegative on the domain of the triple type `a ≤ b ≤ c`; the variables
`u`, `v`, `t` are the inner products of the pairs with the classes `(a, b)`, `(a, c)`, `(b, c)`. -/
noncomputable def domGens (Dm : Dom) (a b c : Nat) : List Gen :=
  loGen (Dm.iv a b) 1 0 0 :: hiGen (Dm.iv a b) 1 0 0 :: loGen (Dm.iv a c) 0 1 0 :: hiGen (Dm.iv a c) 0 1 0
    :: loGen (Dm.iv b c) 0 0 1 :: hiGen (Dm.iv b c) 0 0 1 :: detGen :: csGenU :: csGenV :: csGenT
    :: csGenUm :: csGenVm :: csGenTm :: findCuts a b c Dm.cuts

/-- The denominators of the interval are positive, and the interval lies in the box
`[(cp - cn - rho) / 2 ^ m, (cp - cn + rho) / 2 ^ m]`. -/
def boxIn (P : Params) (b : Box) (I : Ival) : Bool :=
  Nat.ble 1 I.ld && Nat.ble 1 I.hd
    && Nat.ble (Nat.add (Nat.mul b.cp I.ld) (Nat.shiftLeft I.ln P.m))
      (Nat.add (Nat.shiftLeft I.lp P.m) (Nat.mul (Nat.add b.cn b.rho) I.ld))
    && Nat.ble (Nat.add (Nat.shiftLeft I.hp P.m) (Nat.mul b.cn I.hd))
      (Nat.add (Nat.shiftLeft I.hn P.m) (Nat.mul (Nat.add b.cp b.rho) I.hd))

noncomputable def cutsOk : List Cuts → Bool := List.rec true (fun X _ ih => gensOk X.gens && ih)

/-- The domain of the checker contains the domain of the source: for every pair type that occurs the box
contains the interval, the generators of all weights of a triple type are among `domGens`, and the degree
of a cut bounds the degrees of its terms. -/
noncomputable def domOk (P : Params) (C : Cert) (Dm : Dom) (xs : List TyX) : Bool :=
  all2N (fun a b => Nat.blt b a || Nat.beq (pcnt C a b) 0 || boxIn P (C.box a b) (Dm.iv a b)) P.q
    && allX (fun X => weightsIn (domGens Dm X.a X.b X.c) X.weights) xs
    && cutsOk Dm.cuts

/-! ## The sign conditions -/

/-- The witness of the sign condition of a pair type: an instance of `CAP.UniPos.checkPoly` for the
polynomial `den ^ (D + 1) * (2 ^ sP - (2 - 2 t) * Hs t)` in the variable `y = den * t`. -/
structure Sign where
  pp : CAP.UniPos.PParams
  Pp : Nat
  c0 : Nat
  cuts : List Nat
  den : Nat

/-- The digit `j` of a pair polynomial; beyond the degree `D` the bias, which stands for `0`. -/
def hDig (P : Params) (H j : Nat) : Nat :=
  cond (Nat.ble j P.D) (slot P.wP H j) (Nat.shiftLeft 1 (Nat.pred P.wP))

/-- The coefficient `j` of the witness is that of `den ^ n * (2 ^ sP - (2 - 2 t) * Hs t)`, `n = D + 1`: with
the digits `A` of the pair polynomial (`A (-1)` and `A n` are the bias) and `pw = den ^ (n - j)`,
`slot j + 2 * pw * A j = 2 ^ (aH - 1) + 2 * pw * A (j - 1) + [j = 0] * den ^ n * 2 ^ sP`. -/
noncomputable def linkAt (P : Params) (sP H : Nat) (S : Sign) (j : Nat) : Bool :=
  Nat.beq
    (Nat.add (slot S.pp.W S.Pp j) (Nat.mul (Nat.mul 2 (Nat.pow S.den (Nat.sub (Nat.succ P.D) j))) (hDig P H j)))
    (Nat.add
      (Nat.add (Nat.shiftLeft 1 (Nat.pred S.pp.aH))
        (Nat.mul (Nat.mul 2 (Nat.pow S.den (Nat.sub (Nat.succ P.D) j)))
          (Nat.rec (motive := fun _ => Nat) (Nat.shiftLeft 1 (Nat.pred P.wP)) (fun i _ => hDig P H i) j)))
      (Nat.rec (motive := fun _ => Nat) (Nat.shiftLeft (Nat.pow S.den (Nat.succ P.D)) sP) (fun _ _ => 0) j))

/-- The last element of a list of cuts; `prev` for the empty list. -/
noncomputable def lastK : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun prev => prev) (fun c _ ih _ => ih c)

/-- The sign condition of a pair type: on the interval `I`, `(2 - 2 t) * Hs t ≤ 2 ^ sP` for the
polynomial `Hs` with the signed digits of `H`. -/
noncomputable def signOk (P : Params) (sP H : Nat) (I : Ival) (S : Sign) : Bool :=
  CAP.UniPos.checkPoly S.pp S.Pp S.c0 S.cuts
    && Nat.beq S.pp.n (Nat.succ P.D) && allN (linkAt P sP H S) (Nat.succ (Nat.succ P.D))
    && Nat.ble 1 S.den && Nat.ble 1 I.ld && Nat.ble 1 I.hd
    && Nat.ble (Nat.add (Nat.mul I.ld S.c0) (Nat.mul (Nat.shiftLeft S.den S.pp.s) I.ln))
      (Nat.add (Nat.mul I.ld S.pp.off) (Nat.mul (Nat.shiftLeft S.den S.pp.s) I.lp))
    && Nat.ble (Nat.add (Nat.mul (Nat.shiftLeft S.den S.pp.s) I.hp) (Nat.mul I.hd S.pp.off))
      (Nat.add (Nat.mul I.hd (lastK S.cuts S.c0)) (Nat.mul (Nat.shiftLeft S.den S.pp.s) I.hn))

/-- The sign conditions of all pair types that occur. -/
noncomputable def signsOk (P : Params) (C : Cert) (Dm : Dom) (sP : Nat) (sg : Nat → Nat → Sign) : Bool :=
  all2N (fun a b => Nat.blt b a || Nat.beq (pcnt C a b) 0 || signOk P sP (C.H a b) (Dm.iv a b) (sg a b)) P.q

/-! ## The claims -/

/-- The witness of a cap bound for a pair type `(a, b)`: `kind = 0` if the lower end of the interval of
the domain is at most that of the claim; `kind = 1` (`2`) for the cap bound through the partner of the
point of the class `a` (`b`) in the one-edge type `(w1, w2)`, with the witness `lp / lq`. -/
structure CapW where
  kind : Nat
  w1 : Nat
  w2 : Nat
  lp : Nat
  lq : Nat

/-- The witness of a support cut: the root is the point number `root` of the triple, `(w1, w2)` is the
one-edge type of the root, the cut is `kap * (the two inner products of the root) + B * (the third inner
product) + G`, and `ap / aq` is the witness. -/
structure SupW where
  root : Nat
  w1 : Nat
  w2 : Nat
  kap : Nat
  B : Nat
  G : Nat
  ap : Nat
  aq : Nat

/-- A claim: the interval of every pair type `a ≤ b`, the witnesses of the cap bounds and of the support
cuts, and the separation bound `tp / tq`. -/
structure Claim where
  K : Nat → Nat → Ival
  cap : Nat → Nat → CapW
  sup : List SupW
  tp : Nat
  tq : Nat

/-- The pair type `(w1, w2)` of classes below `q` has exactly one pair of points. -/
def oneEdge (q : Nat) (C : Cert) (w1 w2 : Nat) : Bool :=
  Nat.blt w2 q
    && ((Nat.beq w1 w2 && Nat.beq (C.n w1) 2) || (Nat.blt w1 w2 && Nat.beq (C.n w1) 1 && Nat.beq (C.n w2) 1))

/-- The class of the partner of a point of the class `a` in the one-edge type `(w1, w2)`. -/
def partnerOf (w1 w2 a : Nat) : Nat := cond (Nat.beq a w1) w2 w1

def inEdge (w1 w2 a : Nat) : Bool := Nat.beq a w1 || Nat.beq a w2

/-- `hi I ≤ tp / tq` -/
def hiLe (I : Ival) (tp tq : Nat) : Bool :=
  Nat.ble (Nat.mul I.hp tq) (Nat.add (Nat.mul I.hn tq) (Nat.mul tp I.hd))

/-- `hi K ≤ hi J` -/
def hiLeHi (K J : Ival) : Bool :=
  Nat.ble (Nat.add (Nat.mul K.hp J.hd) (Nat.mul J.hn K.hd)) (Nat.add (Nat.mul J.hp K.hd) (Nat.mul K.hn J.hd))

/-- `lo J ≤ lo K` -/
def loLeLo (J K : Ival) : Bool :=
  Nat.ble (Nat.add (Nat.mul J.lp K.ld) (Nat.mul K.ln J.ld)) (Nat.add (Nat.mul K.lp J.ld) (Nat.mul J.ln K.ld))

/-- The cap bound with the witness `a = lp / lq` gives the lower end of `J`: with `T = tp / tq`,
`c = -(hi Kw)` and `m = -(lo J) - a T`, the check is `m ≥ 0` and `1 + a² - 2 a c ≤ m²`, with the
denominators cleared. -/
def capIneq (J Kw : Ival) (lp lq tp tq : Nat) : Bool :=
  Nat.ble (Nat.add (Nat.mul (Nat.mul J.lp lq) tq) (Nat.mul (Nat.mul lp tp) J.ld)) (Nat.mul (Nat.mul J.ln lq) tq)
    && (fun Mn =>
        Nat.ble
          (Nat.mul (Nat.add (Nat.add (Nat.mul (Nat.mul lq lq) Kw.hd) (Nat.mul (Nat.mul lp lp) Kw.hd))
              (Nat.mul (Nat.mul 2 (Nat.mul lp lq)) Kw.hp))
            (Nat.mul (Nat.mul J.ld J.ld) (Nat.mul tq tq)))
          (Nat.add (Nat.mul (Nat.mul Mn Mn) Kw.hd)
            (Nat.mul (Nat.mul (Nat.mul 2 (Nat.mul lp lq)) Kw.hn) (Nat.mul (Nat.mul J.ld J.ld) (Nat.mul tq tq)))))
      (Nat.sub (Nat.mul (Nat.mul J.ln lq) tq) (Nat.add (Nat.mul (Nat.mul J.lp lq) tq) (Nat.mul (Nat.mul lp tp) J.ld)))

/-- The lower end of `J` for the pair type `(a, b)`: it is at most that of the interval `K` of the claim
(`kind = 0`), or it is a cap bound through the partner of the point of the class `a` (`kind = 1`) or of the
class `b` (`kind ≥ 2`), whose class differs from the class of the other point. -/
noncomputable def capLow (q : Nat) (C : Cert) (Cl : Claim) (J K : Ival) (w : CapW) (a b : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) (loLeLo J K)
    (fun i _ => Nat.ble 1 w.lq && oneEdge q C w.w1 w.w2 && Nat.ble 1 (Cl.K w.w1 w.w2).hd
      && Nat.rec (motive := fun _ => Bool)
          (inEdge w.w1 w.w2 a && not (Nat.beq (partnerOf w.w1 w.w2 a) b))
          (fun _ _ => inEdge w.w1 w.w2 b && not (Nat.beq (partnerOf w.w1 w.w2 b) a)) i
      && capIneq J (Cl.K w.w1 w.w2) w.lp w.lq Cl.tp Cl.tq)
    w.kind

/-- The condition (D1) for the pair type `(a, b)`, and the interval of the claim lies below the separation
bound. -/
noncomputable def capOk (q : Nat) (C : Cert) (Dm : Dom) (Cl : Claim) (a b : Nat) : Bool :=
  (fun J => (fun K =>
    Nat.ble 1 K.ld && Nat.ble 1 K.hd && Nat.ble 1 J.ld && Nat.ble 1 J.hd && hiLe K Cl.tp Cl.tq && hiLeHi K J
      && capLow q C Cl J K (Cl.cap a b) a b)
    (Cl.K a b)) (Dm.iv a b)

/-- The support polynomial of a witness: its two equal coefficients belong to the inner products of the
root with the two other points. -/
noncomputable def supGen (w : SupW) : Gen :=
  Nat.rec (motive := fun _ => Gen) ⟨1, [⟨w.G, 0, 0, 0, 0⟩, ⟨w.B, 0, 0, 0, 1⟩, ⟨w.kap, 0, 0, 1, 0⟩, ⟨w.kap, 0, 1, 0, 0⟩]⟩
    (fun i _ => Nat.rec (motive := fun _ => Gen)
      ⟨1, [⟨w.G, 0, 0, 0, 0⟩, ⟨w.kap, 0, 0, 0, 1⟩, ⟨w.B, 0, 0, 1, 0⟩, ⟨w.kap, 0, 1, 0, 0⟩]⟩
      (fun _ _ => ⟨1, [⟨w.G, 0, 0, 0, 0⟩, ⟨w.kap, 0, 0, 0, 1⟩, ⟨w.kap, 0, 0, 1, 0⟩, ⟨w.B, 0, 1, 0, 0⟩]⟩) i)
    w.root

/-- The constant of a support cut is large enough: with `β = B / kap`, `γ = G / kap`, `α = ap / aq`,
`T = tp / tq` and `c = -(hi Kw)`, the check is `2 β γ ≥ 2 β² + 4 α β T + 1 + α² - 2 α c`, with the
denominators cleared. -/
def supIneq (Kw : Ival) (w : SupW) (tp tq : Nat) : Bool :=
  Nat.ble
    (Nat.add (Nat.add (Nat.add
        (Nat.mul (Nat.mul (Nat.mul (Nat.mul 2 (Nat.mul w.B w.B)) (Nat.mul w.aq w.aq)) tq) Kw.hd)
        (Nat.mul (Nat.mul (Nat.mul (Nat.mul w.kap w.kap) (Nat.add (Nat.mul w.aq w.aq) (Nat.mul w.ap w.ap))) tq) Kw.hd))
        (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul (Nat.mul 4 w.ap) w.aq) w.B) tp) w.kap) Kw.hd))
      (Nat.mul (Nat.mul (Nat.mul (Nat.mul 2 (Nat.mul w.kap w.kap)) (Nat.mul w.ap w.aq)) Kw.hp) tq))
    (Nat.add (Nat.mul (Nat.mul (Nat.mul (Nat.mul 2 (Nat.mul w.B w.G)) (Nat.mul w.aq w.aq)) tq) Kw.hd)
      (Nat.mul (Nat.mul (Nat.mul (Nat.mul 2 (Nat.mul w.kap w.kap)) (Nat.mul w.ap w.aq)) Kw.hn) tq))

/-- The classes of the root and of the two other points of a triple type for the root number `r`. -/
noncomputable def rootCls (a b c r : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) a (fun i _ => Nat.rec (motive := fun _ => Nat) b (fun _ _ => c) i) r

noncomputable def restCls1 (a b _c r : Nat) : Nat := Nat.rec (motive := fun _ => Nat) b (fun _ _ => a) r

noncomputable def restCls2 (_a b c r : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) c (fun i _ => Nat.rec (motive := fun _ => Nat) c (fun _ _ => b) i) r

/-- The cut `g` of the triple type `(a, b, c)` is the support polynomial of the witness `w`, and the
witness is admissible. -/
noncomputable def supOk (q : Nat) (C : Cert) (Cl : Claim) (a b c : Nat) (g : Gen) (w : SupW) : Bool :=
  genBeq g (supGen w) && Nat.ble w.root 2 && Nat.ble 1 w.kap && Nat.ble 1 w.B && Nat.ble 1 w.aq
    && oneEdge q C w.w1 w.w2 && inEdge w.w1 w.w2 (rootCls a b c w.root)
    && not (Nat.beq (partnerOf w.w1 w.w2 (rootCls a b c w.root)) (restCls1 a b c w.root))
    && not (Nat.beq (partnerOf w.w1 w.w2 (rootCls a b c w.root)) (restCls2 a b c w.root))
    && Nat.ble 1 (Cl.K w.w1 w.w2).hd && supIneq (Cl.K w.w1 w.w2) w Cl.tp Cl.tq

noncomputable def anySup (f : SupW → Bool) : List SupW → Bool := List.rec false (fun w _ ih => f w || ih)

noncomputable def allGen (f : Gen → Bool) : List Gen → Bool := List.rec true (fun g _ ih => f g && ih)

noncomputable def allCuts (f : Cuts → Bool) : List Cuts → Bool := List.rec true (fun X _ ih => f X && ih)

/-- **The domain contains the claim**: the conditions (D1) and (D2) of the source. The separation bound
is below `1`, every pair type that occurs satisfies (D1), and every cut of the domain is a support
polynomial with an admissible witness. -/
noncomputable def claimOk (P : Params) (C : Cert) (Dm : Dom) (Cl : Claim) : Bool :=
  Nat.ble 1 Cl.tq && Nat.blt Cl.tp Cl.tq
    && all2N (fun a b => Nat.blt b a || Nat.beq (pcnt C a b) 0 || capOk P.q C Dm Cl a b) P.q
    && allCuts (fun X => allGen (fun g => anySup (supOk P.q C Cl X.a X.b X.c g) Cl.sup) X.gens) Dm.cuts

/-! ## Tables -/

noncomputable def nthC : List CapW → Nat → CapW :=
  List.rec (motive := fun _ => Nat → CapW) (fun _ => ⟨0, 0, 0, 0, 0⟩)
    (fun h _ ih i => Nat.rec (motive := fun _ => CapW) h (fun j _ => ih j) i)

noncomputable def nthI : List Ival → Nat → Ival :=
  List.rec (motive := fun _ => Nat → Ival) (fun _ => ⟨0, 0, 0, 0, 0, 0⟩)
    (fun h _ ih i => Nat.rec (motive := fun _ => Ival) h (fun j _ => ih j) i)

noncomputable def nthS : List Sign → Nat → Sign :=
  List.rec (motive := fun _ => Nat → Sign) (fun _ => ⟨⟨0, 0, 0, 0, 0, 0, 0⟩, 0, 0, [], 0⟩)
    (fun h _ ih i => Nat.rec (motive := fun _ => Sign) h (fun j _ => ih j) i)

/-- A domain from tables: the interval of the pair `(a, b)` has the index `a * q + b`. -/
noncomputable def Dom.ofLists (q : Nat) (iv : List Ival) (cuts : List Cuts) : Dom :=
  ⟨fun a b => nthI iv (Nat.add (Nat.mul a q) b), cuts⟩

/-- A claim from tables with the same index. -/
noncomputable def Claim.ofLists (q : Nat) (K : List Ival) (cap : List CapW) (sup : List SupW) (tp tq : Nat) : Claim :=
  ⟨fun a b => nthI K (Nat.add (Nat.mul a q) b), fun a b => nthC cap (Nat.add (Nat.mul a q) b), sup, tp, tq⟩

/-- The witnesses of the sign conditions from a table with the same index. -/
noncomputable def signOf (q : Nat) (l : List Sign) (a b : Nat) : Sign := nthS l (Nat.add (Nat.mul a q) b)

end CAP.Wsos
