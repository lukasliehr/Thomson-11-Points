module

public import CAP.Wsos.CertKernel
public import CAP.UniPos.Kernel

/-!
# Typed three-point certificates on the two-sphere: the checkers (`Init` and kernel modules only)

**State.** The checkers are bit-exact with `N11/ParallelResearch1/cert/ref.py`. The theorems of soundness are
`N11.Circ.checkTy2_sound` (`Sound.lean`), `N11.Circ.boundOk2_sound` (`BoundValue.lean`) and
`N11.Circ.signOk2_sound` (`Minorant.lean`).

The file is a variant of `CAP/Wsos/Kernel.lean`, `Cert.lean` and `CertKernel.lean` (the typed certificates of
the theorem for nine points on the three-sphere). Its structures and all functions that are not defined here
are those of these files. Three things differ.

**The kernels of the circle.** For points of the two-sphere the orthogonal complement of a root is a plane,
and the kernels of a rooted form are `R 0 = 1`, `R 1 = A`, `R (k + 1) = 2 A R k - W R (k - 1)` with
`A = t - u v` and `W = (1 - u²) (1 - v²)`: for two vectors `a`, `b` of the plane with `A = ⟨a, b⟩` and
`W = |a|² |b|²` they are `Re ((a₁ + i a₂) ^ k (b₁ - i b₂) ^ k)`. `checkTy2` is `CAP.Wsos.checkTy` with this
recurrence (`qnext2`), without the factors `d! / k!`, and with the bound for the coefficients that belongs to
it (`rhoL2`).

**The root.** The classes of a certificate are `0, …, q - 2`; the index class `Q = q - 1` of a rooted block is
the root itself, and no point has this class. The share equation of a pair type uses the blocks `(Q, b)` of
the Gram matrices, and the bound uses the block `(Q, Q)` (`shareOf2`, `rootDiag2`).

**The potential.** The certificate bounds the sum of the pair polynomials `K` of the pairs of points. A pair
type has a polynomial `pen` of degree two (`Pen`), and the sign condition of the pair type is

  `K t + pen t ≤ (2 - 2 t) ^ (-1/2)` on its interval,

so that the sum of `(2 - 2 t) ^ (-1/2) - pen t` over the pairs is at least the bound. The witness (`Sign2`)
is the polynomial `Ĥ = Dn (K + pen)` with integer coefficients, `Dn = 2 ^ sP * sc`, and cut points
`1 - lam / 2 ^ s` that cover the interval; on every piece the test is `CAP.UniPos.intervalOk`
(`(2 - 2 t) Ĥ² ≤ Dn²`) or `negOk` (`Ĥ ≤ 0`; a pair polynomial of a cell without configurations can be far below
the potential).
-/

@[expose] public section

namespace N11.Circ

open CAP CAP.Wsos

/-! ## The rooted forms with the kernels of the circle -/

/-- `c * Ah * cur - Wh * prev` modulo `2 ^ M`, with `c = 1` for `k = 0` and `c = 2` otherwise -/
def qnext2 (pM mM Ah Wh k prev cur : Nat) : Nat :=
  Nat.land (subM pM mM (Nat.mul (cond (Nat.beq k 0) 1 2) (mulM mM Ah cur)) (mulM mM Wh prev)) mM

noncomputable def ql2 (pM mM Ah Wh : Nat) : Nat → Nat → Nat → Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List Nat) (fun _ _ _ => [])
    (fun _ ih k prev cur => cur :: ih (Nat.succ k) cur (qnext2 pM mM Ah Wh k prev cur))

/-- the kernels `2 ^ (2 m k) * R k` for `k ≤ d` at `(w1, w2, w3)` -/
noncomputable def qlist2 (P : Params) (pM mM w1 w2 w3 : Nat) : List Nat :=
  ql2 pM mM (Nat.land (subM pM mM (Nat.shiftLeft w3 P.m) (mulM mM w1 w2)) mM)
    (mulM mM (subM pM mM (Nat.shiftLeft 1 (Nat.mul 2 P.m)) (mulM mM w1 w1))
      (subM pM mM (Nat.shiftLeft 1 (Nat.mul 2 P.m)) (mulM mM w2 w2)))
    (Nat.succ P.d) 0 0 1

/-- `∑ k, (2 ^ (2 m k) R k) * ∑ i j, G k ((b, i), (c, j)) * w1 ^ i * w2 ^ j`, homogeneous -/
noncomputable def rootedVal2 (P : Params) (pM mM : Nat) (R : Rooted) (w1 w2 w3 : Nat) (pw1 pw2 : List Nat) : Nat :=
  rootedGo P pM mM pw1 pw2 R.b R.c R.gram (qlist2 P pM mM w1 w2 w3) (rep 1 (Nat.succ P.d)) P.d 0

/-! ## The bound for the coefficients -/

noncomputable def rhoL2 : Nat → Nat → Nat → Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List Nat) (fun _ _ _ => [])
    (fun _ ih k prev cur => cur :: ih (Nat.succ k) cur (Nat.add (Nat.mul (cond (Nat.beq k 0) 1 2) cur) prev))

noncomputable def nRooted2 (P : Params) : Nat :=
  Nat.shiftLeft (kSum (rhoL2 (Nat.succ P.d) 0 0 1) P.d 0 0) (Nat.add (Nat.pred P.wG) (Nat.mul P.m P.D))

/-- A bound for the sum of the absolute values of the coefficients of `2 ^ D` times the residual
and of the Chebyshev combination; `sp`, `sn` are the sums of the coefficients `Np`, `Nn`. -/
noncomputable def bound2 (P : Params) (T : Ty) (sp sn : Nat) : Nat :=
  Nat.add
    (Nat.shiftLeft
      (Nat.add (Nat.add (Nat.add
        (Nat.add
          (Nat.add (Nat.add (Nat.mul (Nat.mul T.s2.mult T.s3.mult) (nShare P T.s1))
            (Nat.mul (Nat.mul T.s1.mult T.s3.mult) (nShare P T.s2))) (Nat.mul (Nat.mul T.s1.mult T.s2.mult) (nShare P T.s3)))
          (Nat.shiftLeft (Nat.mul (Nat.mul 2 (Nat.mul (Nat.mul T.s1.mult T.s2.mult) T.s3.mult))
            (Nat.mul 3 (nRooted2 P))) P.aF))
        T.c2p) T.c2n) (nWeightsGo P T.weights 0))
      P.D)
    (Nat.mul (Nat.add sp sn) (Nat.pow 3 P.D))

/-! ## The checker of a triple type -/

noncomputable def residualK2 (P : Params) (T : Ty) (pM mM u v t : Nat) (pu pv pt : List Nat) : Nat :=
  subM pM mM
    (Nat.add (Nat.add (Nat.add
      (Nat.mul (Nat.mul T.s2.mult T.s3.mult) (shareVal P pM mM 1 T.s1 u pu))
      (Nat.mul (Nat.mul T.s1.mult T.s3.mult) (shareVal P pM mM 1 T.s2 v pv)))
      (Nat.mul (Nat.mul T.s1.mult T.s2.mult) (shareVal P pM mM 1 T.s3 t pt))) T.c2n)
    (Nat.add (Nat.add
      (Nat.shiftLeft (Nat.mul (Nat.mul 2 (Nat.mul (Nat.mul T.s1.mult T.s2.mult) T.s3.mult))
        (Nat.land (Nat.add (Nat.add (rootedVal2 P pM mM T.r1 u v t pu pv) (rootedVal2 P pM mM T.r2 u t v pu pt))
          (rootedVal2 P pM mM T.r3 v t u pv pt)) mM)) P.aF)
      T.c2p)
      (weightsGo P pM mM u v t (monoGo P.W (Nat.mul P.W P.k1) (Nat.mul P.W P.k2) (Nat.succ P.d) 1 1 1) T.weights 0))

noncomputable def residualU2 (P : Params) (T : Ty) (pM mM u v t : Nat) : Nat :=
  residualK2 P T pM mM u v t (pows mM u (Nat.succ P.D) 1) (pows mM v (Nat.succ P.D) 1) (pows mM t (Nat.succ P.D) 1)

/-- The number of the residual `Λ - c - ∑ weights` modulo `2 ^ M`. -/
noncomputable def residual2 (P : Params) (T : Ty) (pM mM : Nat) : Nat :=
  residualU2 P T pM mM (aff pM mM T.bu (Nat.shiftLeft 1 P.W)) (aff pM mM T.bv (Nat.shiftLeft 1 (Nat.mul P.W P.k1)))
    (aff pM mM T.bt (Nat.shiftLeft 1 (Nat.mul P.W P.k2)))

noncomputable def checkK2 (P : Params) (T : Ty) (pM mM sp sn : Nat) : Bool :=
  flags P T && Nat.blt (bound2 P T sp sn) (Nat.shiftLeft 1 (Nat.pred P.W))
    && Nat.beq (Nat.land (Nat.shiftLeft (residual2 P T pM mM) P.D) mM)
        (Nat.land (subM pM mM (chebVal P pM mM T.Np) (chebVal P pM mM T.Nn)) mM)
    && Nat.ble (Nat.add sp sn) (Nat.mul 2 (Nat.land T.Np (mask P.wN)))

/-- The checker of a triple type, with the kernels of the circle. -/
noncomputable def checkTy2 (P : Params) (T : Ty) : Bool :=
  (fun pM => checkK2 P T pM (Nat.sub pM 1) (chebSum P T.Np) (chebSum P T.Nn)) (Nat.shiftLeft 1 (Nat.mul P.W P.slots))

/-! ## The record of a triple type: the root has the index class `Q` -/

/-- The share of the pair type `(a, b)` for the third class `c`. For `c = last a b` it is the share of the
share equation, in which the root of a rooted block has the index class `Q`. -/
noncomputable def shareOf2 (Q : Nat) (C : Cert) (a b c : Nat) : Share :=
  cond (Nat.beq c (C.last a b))
    ⟨mult C a b c, C.H a b, tab (C.p a b) c, tab (mult C a b) c, [⟨C.gram a, Q, b⟩, ⟨C.gram b, Q, a⟩]⟩
    ⟨1, C.p a b c, [], [], []⟩

/-- The record of the triple type for the checker. -/
noncomputable def tyOf2 (Q : Nat) (C : Cert) (X : TyX) : Ty :=
  ⟨C.box X.a X.b, C.box X.a X.c, C.box X.b X.c, shareOf2 Q C X.a X.b X.c, shareOf2 Q C X.a X.c X.b,
    shareOf2 Q C X.b X.c X.a, ⟨C.gram X.a, X.b, X.c⟩, ⟨C.gram X.b, X.a, X.c⟩, ⟨C.gram X.c, X.a, X.b⟩,
    X.weights, X.c2p, X.c2n, X.Np, X.Nn⟩

/-! ## The bound -/

/-- The sum of the slots of the block `(Q, Q)`, `Q = q - 1`, of the Gram matrix of degree `0` of the class `a`. -/
noncomputable def rootDiag2 (P : Params) (C : Cert) (a : Nat) : Nat :=
  linGo P.wG (mask P.wG) (Nat.succ P.d) (Nat.mul P.wG (Nat.mul P.q (Nat.succ P.d))) (rep 1 (Nat.succ P.d))
    (Nat.shiftRight (hd (C.gram a)) (Nat.mul P.wG (Nat.add (Nat.mul (Nat.pred P.q) (Nat.succ P.d))
      (Nat.mul (Nat.mul P.q (Nat.succ P.d)) (Nat.mul (Nat.pred P.q) (Nat.succ P.d)))))) 0

/-- `6 * M * 2 ^ (aF + 2 m d)` -/
noncomputable def bR2 (P : Params) (M : Nat) : Nat :=
  Nat.mul (Nat.mul 6 M) (Nat.shiftLeft 1 (Nat.add P.aF (Nat.mul (Nat.mul 2 P.m) P.d)))

/-- The bound of the certificate exceeds `tp / tq`:
`6 M 2 ^ (m D + aP + sP) tp + tq (Sn + R Gp) < tq (Sp + R Gn)` with `R = 6 M 2 ^ (aF + 2 m d)`, where
`Sp - Sn = ∑ cnt c2 (M / μ)` over the triples of classes and `Gp - Gn = ∑ n a * g a` for the sums `g a` of the
entries of the blocks `(Q, Q)`. -/
noncomputable def boundOk2 (P : Params) (C : Cert) (xs : List TyX) (sP M tp tq : Nat) : Bool :=
  Nat.ble 1 M && Nat.ble 1 tq && all3N (divOk C xs M) P.q
    && Nat.blt
      (Nat.add (Nat.mul (Nat.mul (Nat.mul 6 M) (Nat.shiftLeft 1 (Nat.add (Nat.add (Nat.mul P.m P.D) P.aP) sP))) tp)
        (Nat.mul tq (Nat.add (sum3N (cTerm C xs M fun X => X.c2n) P.q)
          (Nat.mul (bR2 P M) (sumN (fun a => Nat.mul (C.n a) (rootDiag2 P C a)) P.q)))))
      (Nat.mul tq (Nat.add (sum3N (cTerm C xs M fun X => X.c2p) P.q)
        (Nat.mul (bR2 P M) (sumN (fun a => Nat.mul (C.n a) (rootNeg P)) P.q))))

/-! ## The sign conditions -/

/-- The polynomial `pen` of a pair type: `Dn * pen t = (a0p - a0n) + (a1p - a1n) * t + (a2p - a2n) * t ^ 2`. -/
structure Pen where
  a0p : Nat
  a0n : Nat
  a1p : Nat
  a1n : Nat
  a2p : Nat
  a2n : Nat

/-- The witness of the sign condition of a pair type: the polynomial `Dn * (K + pen)` as the packed number
`Hp` of `CAP.UniPos` (slot width `pp.W`, bias `2 ^ (pp.aH - 1)`), `Dn = 2 ^ sP * sc`, and the cut points
`1 - lam / 2 ^ pp.s` for `lam = lam0` and for the cuts of the entries of `cuts` (an entry is twice the cut plus the
kind of the test of its piece), which decrease. -/
structure Sign2 where
  pp : CAP.UniPos.Params
  Hp : Nat
  sc : Nat
  pen : Pen
  lam0 : Nat
  cuts : List Nat

def penP (p : Pen) (j : Nat) : Nat := cond (Nat.beq j 0) p.a0p (cond (Nat.beq j 1) p.a1p (cond (Nat.beq j 2) p.a2p 0))

def penN (p : Pen) (j : Nat) : Nat := cond (Nat.beq j 0) p.a0n (cond (Nat.beq j 1) p.a1n (cond (Nat.beq j 2) p.a2n 0))

/-- The coefficient `j` of the witness is `sc` times the coefficient `j` of the pair polynomial plus the
coefficient `j` of `Dn * pen`:
`slot j of Hp + sc * 2 ^ (wP - 1) + penN j = sc * (slot j of H) + penP j + 2 ^ (aH - 1)`. -/
def linkAt2 (P : Params) (H : Nat) (S : Sign2) (j : Nat) : Bool :=
  Nat.beq
    (Nat.add (Nat.add (slot S.pp.W S.Hp j) (Nat.mul S.sc (Nat.shiftLeft 1 (Nat.pred P.wP)))) (penN S.pen j))
    (Nat.add (Nat.add (Nat.mul S.sc (slot P.wP H j)) (penP S.pen j)) (Nat.shiftLeft 1 (Nat.pred S.pp.aH)))

/-- `Ĥ ≤ 0` on the piece between the cuts `lk > lk1`, for the polynomial `Ĥ` of the witness: with the variable of
`CAP.UniPos`, `(2 ^ s (1 + y)) ^ (2 D) Ĥ = Hb (y)` is a difference of two polynomials with natural coefficients, and
the coefficients of the positive part are at most those of the negative part. -/
noncomputable def negOk (pp : CAP.UniPos.Params) (Hp lk lk1 : Nat) : Bool :=
  Nat.blt (CAP.UniPos.hornerGo pp 0 Hp lk lk1 (Nat.succ (Nat.mul 2 pp.D)) 0 0 1).1 (Nat.shiftLeft 1 (Nat.sub pp.V 1))
    && Nat.blt (CAP.UniPos.hornerGo pp 0 Hp lk lk1 (Nat.succ (Nat.mul 2 pp.D)) 0 0 1).2 (Nat.shiftLeft 1 (Nat.sub pp.V 1))
    && CAP.UniPos.geTest pp.V (Nat.add (Nat.mul 2 pp.D) 2)
        (CAP.UniPos.hornerGo pp pp.V Hp lk lk1 (Nat.succ (Nat.mul 2 pp.D)) 0 0 1).2
        (CAP.UniPos.hornerGo pp pp.V Hp lk lk1 (Nat.succ (Nat.mul 2 pp.D)) 0 0 1).1

/-- The loop over the cuts; `prev` is the previous cut. An entry `c` of the list is the cut `c / 2` with the kind
`c % 2` of the test of the piece that ends at it: `0` for `(2 - 2 t) Ĥ² ≤ Dn²` (`CAP.UniPos.intervalOk`), `1` for
`Ĥ ≤ 0` (`negOk`). The cuts decrease. -/
noncomputable def cutsGo2 (pp : CAP.UniPos.Params) (Hp Dn : Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun c _ ih prev => Nat.blt (Nat.div c 2) prev
      && cond (Nat.beq (Nat.mod c 2) 0) (CAP.UniPos.intervalOk pp Hp Dn prev (Nat.div c 2)) (negOk pp Hp prev (Nat.div c 2))
      && ih (Nat.div c 2))

/-- The last cut of a list of entries; `prev` for the empty list. -/
noncomputable def lastCut2 : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun prev => prev) (fun c _ ih _ => ih (Nat.div c 2))

/-- The sign condition of a pair type: `K t + pen t ≤ (2 - 2 t) ^ (-1/2)` on the interval `I`, where `K` has
the signed digits of `H` over `2 ^ sP`. The pieces cover the interval: with `E = 2 ^ pp.s`,
`E (1 - lo) ≤ lam0` and `last cut < E (1 - hi)`. -/
noncomputable def signOk2 (P : Params) (sP H : Nat) (I : Ival) (S : Sign2) : Bool :=
  Nat.ble 1 S.pp.V && Nat.beq (Nat.mul 2 S.pp.D) P.D && Nat.ble 1 S.sc && Nat.ble 1 I.ld && Nat.ble 1 I.hd
    && allN (linkAt2 P H S) (Nat.succ P.D)
    && cutsGo2 S.pp S.Hp (Nat.mul (Nat.shiftLeft 1 sP) S.sc) S.cuts S.lam0
    && Nat.ble (Nat.mul (Nat.shiftLeft 1 S.pp.s) (Nat.add I.ld I.ln))
      (Nat.add (Nat.mul S.lam0 I.ld) (Nat.mul (Nat.shiftLeft 1 S.pp.s) I.lp))
    && Nat.blt (Nat.add (Nat.mul (lastCut2 S.cuts S.lam0) I.hd) (Nat.mul (Nat.shiftLeft 1 S.pp.s) I.hp))
      (Nat.mul (Nat.shiftLeft 1 S.pp.s) (Nat.add I.hd I.hn))

/-- The sign conditions of all pair types that occur. -/
noncomputable def signsOk2 (P : Params) (C : Cert) (Dm : Dom) (sP : Nat) (sg : Nat → Nat → Sign2) : Bool :=
  all2N (fun a b => Nat.blt b a || Nat.beq (pcnt C a b) 0 || signOk2 P sP (C.H a b) (Dm.iv a b) (sg a b)) P.q

noncomputable def nthS : List Sign2 → Nat → Sign2 :=
  List.rec (motive := fun _ => Nat → Sign2) (fun _ => ⟨⟨0, 0, 0, 0, 0⟩, 0, 0, ⟨0, 0, 0, 0, 0, 0⟩, 0, []⟩)
    (fun h _ ih i => Nat.rec (motive := fun _ => Sign2) h (fun j _ => ih j) i)

/-- The witness of the pair type `(a, b)` in a table: the entry `a * q + b`. -/
noncomputable def signOf2 (q : Nat) (l : List Sign2) (a b : Nat) : Sign2 := nthS l (Nat.add (Nat.mul a q) b)

/-- The polynomial `pen` is zero. -/
def penZero (p : Pen) : Bool :=
  Nat.beq p.a0p 0 && Nat.beq p.a0n 0 && Nat.beq p.a1p 0 && Nat.beq p.a1n 0 && Nat.beq p.a2p 0 && Nat.beq p.a2n 0

/-- No witness of the list has a polynomial `pen`: the potential of every pair type is `(2 - 2 t) ^ (-1/2)`. -/
noncomputable def pensZero : List Sign2 → Bool := List.rec true (fun S _ ih => penZero S.pen && ih)

/-! ## The decidable hypotheses on the tables of a certificate -/

/-- The index class `Q = q - 1` of the root is empty; the Gram matrices of every class below `Q` are `d + 1`
in number; the class of the share equation of every pair type is its largest class with further points; the
list contains every triple type that occurs. -/
noncomputable def tablesOk (P : Params) (C : Cert) (xs : List TyX) : Bool :=
  Nat.ble 1 P.q && Nat.beq (C.n (Nat.pred P.q)) 0
    && allN (fun a => Nat.beq (len (C.gram a)) (Nat.succ P.d)) (Nat.pred P.q)
    && all2N (fun a b => Nat.blt b a
        || (Nat.blt (C.last a b) P.q && Nat.blt 0 (mult C a b (C.last a b))
          && allN (fun x => Nat.ble x (C.last a b) || Nat.beq (mult C a b x) 0) P.q)) P.q
    && all3N (fun a b c => Nat.blt b a || Nat.blt c b || Nat.beq (mult C b c a) 0 || Nat.beq (mult C a c b) 0
        || Nat.beq (mult C a b c) 0 || hasX a b c xs) P.q

/-! ## Tables in rows, and checks over lists

A lookup `nth l i` in a list costs the kernel a number of steps proportional to `i`. The tables of
`CAP.Wsos.Cert.ofLists` have `q ^ 2` and `q ^ 3` entries; with tables in rows (the entry of the pair `(a, b)` is
the entry `b` of the row `a`) a lookup costs `a + b + c` steps. The structures are those of the library, so
nothing changes for the theorems. -/

noncomputable def nthBL : List (List Box) → Nat → List Box :=
  List.rec (motive := fun _ => Nat → List Box) (fun _ => [])
    (fun h _ ih i => Nat.rec (motive := fun _ => List Box) h (fun j _ => ih j) i)

noncomputable def nthLL : List (List (List Nat)) → Nat → List (List Nat) :=
  List.rec (motive := fun _ => Nat → List (List Nat)) (fun _ => [])
    (fun h _ ih i => Nat.rec (motive := fun _ => List (List Nat)) h (fun j _ => ih j) i)

noncomputable def nthIL : List (List Ival) → Nat → List Ival :=
  List.rec (motive := fun _ => Nat → List Ival) (fun _ => [])
    (fun h _ ih i => Nat.rec (motive := fun _ => List Ival) h (fun j _ => ih j) i)

noncomputable def nthSL : List (List Sign2) → Nat → List Sign2 :=
  List.rec (motive := fun _ => Nat → List Sign2) (fun _ => [])
    (fun h _ ih i => Nat.rec (motive := fun _ => List Sign2) h (fun j _ => ih j) i)

/-- A certificate from tables in rows. -/
noncomputable def certOfRows (n : List Nat) (box : List (List Box)) (H : List (List Nat)) (p : List (List (List Nat)))
    (gram : List (List Nat)) (last : List (List Nat)) : Cert :=
  ⟨nth n, fun a b => nthB (nthBL box a) b, fun a b => nth (nthL H a) b, fun a b c => nth (nthL (nthLL p a) b) c,
    nthL gram, fun a b => nth (nthL last a) b⟩

/-- A domain without further inequalities from a table of intervals in rows. -/
noncomputable def domOfRows (iv : List (List Ival)) : Dom := ⟨fun a b => nthI (nthIL iv a) b, []⟩

/-- The witness of the pair type `(a, b)` in a table in rows. -/
noncomputable def signOfRows (l : List (List Sign2)) (a b : Nat) : Sign2 := nthS (nthSL l a) b

/-- No witness of the table has a polynomial `pen`. -/
noncomputable def pensZeroR : List (List Sign2) → Bool := List.rec true (fun row _ ih => pensZero row && ih)

/-- A table of numbers for the triples `a ≤ b ≤ c` in rows. -/
noncomputable def constOfRows (t : List (List (List Nat))) (a b c : Nat) : Nat := nth (nthL (nthLL t a) b) c

/-- All triple types of a list are accepted. -/
noncomputable def tysOk (P : Params) (Q : Nat) (C : Cert) : List TyX → Bool :=
  List.rec true (fun X _ ih => checkTy2 P (tyOf2 Q C X) && ih)

/-- The Gram matrices `gs` of a class, for the degrees `n, n - 1, …`, are those of the factors `ys`. -/
noncomputable def gramRowOk (P : Params) : List (List Nat) → Nat → List Nat → Bool :=
  List.rec (motive := fun _ => Nat → List Nat → Bool) (fun _ gs => List.rec true (fun _ _ _ => false) gs)
    (fun y _ ih n gs => List.rec false (fun g gs' _ => gramOk P n y g && ih (Nat.pred n) gs') gs)

/-- The Gram matrices of all classes below `Q` are those of the factors of the table `ys`. -/
noncomputable def gramsOk (P : Params) (C : Cert) (ys : List (List (List Nat))) (Q : Nat) : Bool :=
  allN (fun a => gramRowOk P (nthLL ys a) P.d (C.gram a)) Q

/-! ## The bound with a table of the constants

`boundOk2` finds the triple type of every triple of classes in the list `xs`. Here the constants of the triple
types are read from two tables (`cP`, `cN`, for the sorted triple), and one pass over the list tests that the
tables hold the constants of its entries (`constsOk`). A triple of classes without triples of points costs one
test. -/

/-- The product of the multiplicities of the three shares of the triple type `a ≤ b ≤ c`. -/
def tmultK (C : Cert) (a b c : Nat) : Nat := Nat.mul (Nat.mul (smult C a b c) (smult C a c b)) (smult C b c a)

noncomputable def cTerm3 (C : Cert) (cT : Nat → Nat → Nat → Nat) (M a b c : Nat) : Nat :=
  cond (Nat.beq (cnt C a b c) 0) 0
    (Nat.mul (Nat.mul (cnt C a b c) (cT (lo3 a b c) (mid3 a b c) (hi3 a b c)))
      (Nat.div M (tmultK C (lo3 a b c) (mid3 a b c) (hi3 a b c))))

noncomputable def divOk3 (C : Cert) (M a b c : Nat) : Bool :=
  Nat.beq (cnt C a b c) 0 || Nat.beq (Nat.mod M (tmultK C (lo3 a b c) (mid3 a b c) (hi3 a b c))) 0

/-- The tables hold the constants of the triple types of the list. -/
noncomputable def constsOk (cP cN : Nat → Nat → Nat → Nat) : List TyX → Bool :=
  List.rec true (fun X _ ih => Nat.beq (cP X.a X.b X.c) X.c2p && Nat.beq (cN X.a X.b X.c) X.c2n && ih)

/-- The bound of the certificate exceeds `tp / tq` (as `boundOk2`, with the constants from the tables). -/
noncomputable def boundOk3 (P : Params) (C : Cert) (xs : List TyX) (cP cN : Nat → Nat → Nat → Nat) (sP M tp tq : Nat) : Bool :=
  Nat.ble 1 M && Nat.ble 1 tq && constsOk cP cN xs && all3N (divOk3 C M) P.q
    && Nat.blt
      (Nat.add (Nat.mul (Nat.mul (Nat.mul 6 M) (Nat.shiftLeft 1 (Nat.add (Nat.add (Nat.mul P.m P.D) P.aP) sP))) tp)
        (Nat.mul tq (Nat.add (sum3N (cTerm3 C cN M) P.q)
          (Nat.mul (bR2 P M) (sumN (fun a => Nat.mul (C.n a) (rootDiag2 P C a)) P.q)))))
      (Nat.mul tq (Nat.add (sum3N (cTerm3 C cP M) P.q)
        (Nat.mul (bR2 P M) (sumN (fun a => Nat.mul (C.n a) (rootNeg P)) P.q))))

/-! ## The weights of a box certificate of degree 6

Every triple type of a certificate of route G has the same eight weights: `1` (squares of degree at most 3), the
two end points of the interval of each of its three variables (degree at most 2), and the Gram determinant
(degree at most 1). `stdW` builds them from the domain, so that the module of a certificate contains only the
packed columns and the multipliers of a triple type. Nothing has to be proved about this function: the checks
read the weights that it returns. -/

/-- A weight whose columns are those of an upper triangular factor, stored one after the other in `cd` and
placed by `sp`. -/
noncomputable def wOf (gens : List Gen) (delta r : Nat) (sp : Nat → Nat) (w0 bn cd mul : Nat) : Weight :=
  ⟨gens, delta, r, fun i => sp (colAt w0 bn cd i), mul⟩

/-- The eight weights of the triple type `a ≤ b ≤ c`; `cd` and `mul` hold their packed columns and multipliers. -/
noncomputable def stdW (Dm : Dom) (w0 : Nat) (sp3 sp2 sp1 : Nat → Nat) (bn3 bn2 bn1 r3 r2 r1 : Nat) (a b c : Nat)
    (cd mul : List Nat) : List Weight :=
  [wOf [] 3 r3 sp3 w0 bn3 (nth cd 0) (nth mul 0),
    wOf [loGen (Dm.iv a b) 1 0 0] 2 r2 sp2 w0 bn2 (nth cd 1) (nth mul 1),
    wOf [hiGen (Dm.iv a b) 1 0 0] 2 r2 sp2 w0 bn2 (nth cd 2) (nth mul 2),
    wOf [loGen (Dm.iv a c) 0 1 0] 2 r2 sp2 w0 bn2 (nth cd 3) (nth mul 3),
    wOf [hiGen (Dm.iv a c) 0 1 0] 2 r2 sp2 w0 bn2 (nth cd 4) (nth mul 4),
    wOf [loGen (Dm.iv b c) 0 0 1] 2 r2 sp2 w0 bn2 (nth cd 5) (nth mul 5),
    wOf [hiGen (Dm.iv b c) 0 0 1] 2 r2 sp2 w0 bn2 (nth cd 6) (nth mul 6),
    wOf [detGen] 1 r1 sp1 w0 bn1 (nth cd 7) (nth mul 7)]

end N11.Circ
