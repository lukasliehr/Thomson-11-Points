module

public import N14.Local.Kernel
public import CAP.PSD.Kernel

/-!
# G7 of route G for eleven points, the local constants: the checks (`Init` and kernel modules only)

The data (`Dat`) are a reference configuration `p` of eleven points with dyadic coordinates (`P i c / 2^60`,
signed) and dyadic coefficients `a, b, c` of the pairs (`A i j / 2^60`, …). With `t = <p_i, p_j>` they are
close to the derivatives `f'(t)`, `f''(t) / 2`, `f'''(t) / 6` of the potential `f(t) = (2 - 2 t)^(-1/2)`.

A signed integer is a pair `(p, n)` of natural numbers with the value `p - n` (`zadd`, `zmul`, …). The results of
the operations are pairs of numerals: `zmk` computes both numbers before it forms the pair (`forceN`), so that a
value that is used twice is not computed twice.

A coordinate of a configuration `u` is `u i c` with a point `i < 11` and `c < 3`; its flat index is `3 i + c`
(`pt`, `co`). The tables of the forms:

* `Lu`: the linear form `L_ij(u) = <p_i, u_j> + <u_i, p_j>` (scale `2^60`);
* `psi2`: twice the table of `psi_ij(u) = <u_i, u_j> - (t / 2) (|u_i|² + |u_j|²)` (scale `2^120`);
* `pen`: the table of `∑ <p_i, u_i>² + ∑_{i, j} (t_ij <u_i, u_j> - <p_i, u_j> <u_i, p_j>)`, which for unit `p` is
  `∑ <p_i, u_i>² + |∑ p_i × u_i|²` (scale `2^120`);
* `qtab`: `2^181 (∑_{i<j} (a psi + b L²) + K pen - kappa |u|²)`; `rtab`: `2^120 (∑ L² + K pen - sigma² |u|²)`;
* `Mb`, `Lb`, `Gt`, `Ht`, `psib2`: the same forms with the projections `1 - p_i p_iᵀ` built in;
* `Rraw`: the table of the cubic form `c L³ + 2 b L psi - (a / 2) (<u_i, p_j> |u_j|² + <p_i, u_j> |u_i|²)` of a
  pair (scale `2^600`); `T6`: the sum over the pairs and over the six orders of the three indices.

The checks:

* `hessOk`, `rigOk`: the upper triangle of the symmetric matrix of `qtab` (`rtab`) is the matrix `rows` of E2, and
  the checker of E2 accepts it;
* `tabOk`: the block `a` of the table `tab` holds the numbers `T6 k a b + off` (row `b`, entry `k`); `cubOk`: the
  table has the shape `33 × 33 × 33` and the checker of E2 accepts the matrix `rows`; `wEntOk`: an entry of the
  upper triangle of `rows` is that of `c3s [a = a'] - ∑_{b, k} T6 k a b * T6 k a' b`, computed from `tab` with the
  rows in step;
* `encOk`: the enclosures of `a, b, c`; `symOk`; `gradOk`: the residual of the first-order condition;
  `rowsOk`: the row sums of the coefficients; `normOk`: `| |p_i|² - 1 | ≤ e / 2^120`; `topOk`: `t_ij ≤ tmax / 2^120`.

The checks are bit-exact with `N11/g7/gen.py`, which was written first. Soundness: `N11/Local/`.
-/

@[expose] public section

namespace N11.Local

open CAP

/-! ## Signed integers as pairs of natural numbers -/

/-- `f v`, with the number `v` computed first: the kernel reduces the major premise `v + 1` of the recursor to a
numeral and passes the numeral `v` to `f`. -/
noncomputable def forceN {α : Type} (d : α) (v : Nat) (f : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) d (fun n _ => f n) (Nat.add v 1)

/-- The pair `(p, n)`, with both numbers computed. -/
noncomputable def zmk (p n : Nat) : Nat × Nat :=
  forceN (0, 0) p fun p' => forceN (0, 0) n fun n' => (p', n')

noncomputable def zadd (a b : Nat × Nat) : Nat × Nat :=
  Prod.rec (motive := fun _ => Nat × Nat)
    (fun a1 a2 => Prod.rec (motive := fun _ => Nat × Nat)
      (fun b1 b2 => zmk (Nat.add a1 b1) (Nat.add a2 b2)) b) a

noncomputable def zsub (a b : Nat × Nat) : Nat × Nat :=
  Prod.rec (motive := fun _ => Nat × Nat)
    (fun a1 a2 => Prod.rec (motive := fun _ => Nat × Nat)
      (fun b1 b2 => zmk (Nat.add a1 b2) (Nat.add a2 b1)) b) a

noncomputable def zneg (a : Nat × Nat) : Nat × Nat :=
  Prod.rec (motive := fun _ => Nat × Nat) (fun a1 a2 => (a2, a1)) a

noncomputable def zmul (a b : Nat × Nat) : Nat × Nat :=
  Prod.rec (motive := fun _ => Nat × Nat)
    (fun a1 a2 => Prod.rec (motive := fun _ => Nat × Nat)
      (fun b1 b2 => zmk (Nat.add (Nat.mul a1 b1) (Nat.mul a2 b2)) (Nat.add (Nat.mul a1 b2) (Nat.mul a2 b1))) b) a

/-- The product with a natural number. -/
noncomputable def znat (k : Nat) (a : Nat × Nat) : Nat × Nat :=
  forceN (0, 0) k fun k' =>
    Prod.rec (motive := fun _ => Nat × Nat) (fun a1 a2 => zmk (Nat.mul k' a1) (Nat.mul k' a2)) a

noncomputable def zeq (a b : Nat × Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool)
    (fun a1 a2 => Prod.rec (motive := fun _ => Bool) (fun b1 b2 => Nat.beq (Nat.add a1 b2) (Nat.add b1 a2)) b) a

noncomputable def zle (a b : Nat × Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool)
    (fun a1 a2 => Prod.rec (motive := fun _ => Bool) (fun b1 b2 => Nat.ble (Nat.add a1 b2) (Nat.add b1 a2)) b) a

/-- The value `v` if `b` holds, and zero otherwise. -/
noncomputable def ind (b : Bool) (v : Nat × Nat) : Nat × Nat := cond b v (0, 0)

noncomputable def zsum (f : Nat → Nat × Nat) : Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) (0, 0) (fun k ih => zadd ih (f k))

noncomputable def ball (f : Nat → Bool) : Nat → Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => ih && f k)

noncomputable def nsum (f : Nat → Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k ih => Nat.add ih (f k))

/-- The sum over the pairs `i < j < 11`. -/
noncomputable def zsumP (f : Nat → Nat → Nat × Nat) : Nat × Nat :=
  zsum (fun i => zsum (fun j => ind (Nat.blt i j) (f i j)) 11) 11

/-! ## Lists -/

noncomputable def getN : List Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun t _ ih i => Nat.rec (motive := fun _ => Nat) t (fun j _ => ih j) i)

noncomputable def getZ : List (Nat × Nat) → Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat × Nat) (fun _ => (0, 0))
    (fun t _ ih i => Nat.rec (motive := fun _ => Nat × Nat) t (fun j _ => ih j) i)

noncomputable def getLN : List (List Nat) → Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun t _ ih i => Nat.rec (motive := fun _ => List Nat) t (fun j _ => ih j) i)

noncomputable def getLZ : List (List (Nat × Nat)) → Nat → List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => [])
    (fun t _ ih i => Nat.rec (motive := fun _ => List (Nat × Nat)) t (fun j _ => ih j) i)

noncomputable def getLLN : List (List (List Nat)) → Nat → List (List Nat) :=
  List.rec (motive := fun _ => Nat → List (List Nat)) (fun _ => [])
    (fun t _ ih i => Nat.rec (motive := fun _ => List (List Nat)) t (fun j _ => ih j) i)

/-! ## The data -/

/-- The reference configuration and the coefficients of the pairs. -/
structure Dat where
  /-- the coordinates `P i c`, signed, scale `2^60` -/
  P : List (List (Nat × Nat))
  /-- `A i j`, scale `2^60` -/
  A : List (List Nat)
  /-- `B i j`, scale `2^60` -/
  B : List (List Nat)
  /-- `C i j`, scale `2^60` -/
  C : List (List Nat)

noncomputable def gp (D : Dat) (i c : Nat) : Nat × Nat := getZ (getLZ D.P i) c

noncomputable def ga (D : Dat) (i j : Nat) : Nat := getN (getLN D.A i) j

noncomputable def gb (D : Dat) (i j : Nat) : Nat := getN (getLN D.B i) j

noncomputable def gc (D : Dat) (i j : Nat) : Nat := getN (getLN D.C i) j

/-- The point of a flat index. -/
noncomputable def pt (k : Nat) : Nat := Nat.div k 3

/-- The coordinate of a flat index. -/
noncomputable def co (k : Nat) : Nat := Nat.mod k 3

/-- `<P_i, P_j>`, scale `2^120`. -/
noncomputable def tI (D : Dat) (i j : Nat) : Nat × Nat :=
  zadd (zadd (zmul (gp D i 0) (gp D j 0)) (zmul (gp D i 1) (gp D j 1))) (zmul (gp D i 2) (gp D j 2))

/-! ## The quadratic forms -/

/-- The table of `L_ij`, scale `2^60`. -/
noncomputable def Lu (D : Dat) (i j u c : Nat) : Nat × Nat :=
  zadd (ind (Nat.beq u i) (gp D j c)) (ind (Nat.beq u j) (gp D i c))

/-- Twice the table of `psi_ij`, scale `2^120`; `T` is `tI D i j`. -/
noncomputable def psi2 (T : Nat × Nat) (i j u c u' c' : Nat) : Nat × Nat :=
  ind (Nat.beq c c')
    (zsub (ind (Nat.beq u i && Nat.beq u' j) (Nat.shiftLeft 1 121, 0))
      (zadd (ind (Nat.beq u i && Nat.beq u' i) T) (ind (Nat.beq u j && Nat.beq u' j) T)))

/-- The table of the penalty, scale `2^120`. -/
noncomputable def pen (D : Dat) (u c u' c' : Nat) : Nat × Nat :=
  zadd (ind (Nat.beq u u') (zmul (gp D u c) (gp D u c')))
    (zsub (ind (Nat.beq c c') (tI D u u')) (zmul (gp D u c') (gp D u' c)))

/-- The table of `2^181 (∑ (a psi + b L²) + K pen - kappa |u|²)`: `K` is the factor of the penalty times `2^61`,
`kap` is `kappa 2^181`. -/
noncomputable def qtab (D : Dat) (kap K u c u' c' : Nat) : Nat × Nat :=
  zsub
    (zadd
      (zsumP fun i j => Prod.rec (motive := fun _ => Nat × Nat)
        (fun t1 t2 => zadd (znat (ga D i j) (psi2 (t1, t2) i j u c u' c'))
          (znat (Nat.mul 2 (gb D i j)) (zmul (Lu D i j u c) (Lu D i j u' c')))) (tI D i j))
      (znat K (pen D u c u' c')))
    (ind (Nat.beq u u' && Nat.beq c c') (kap, 0))

/-- The table of `2^120 (∑ L² + K pen - sigma² |u|²)`: `sig` is `sigma² 2^120`. -/
noncomputable def rtab (D : Dat) (sig K u c u' c' : Nat) : Nat × Nat :=
  zsub
    (zadd (zsumP fun i j => zmul (Lu D i j u c) (Lu D i j u' c')) (znat K (pen D u c u' c')))
    (ind (Nat.beq u u' && Nat.beq c c') (sig, 0))

/-- The entry `(k, k + s)` of the upper triangle of the symmetric matrix of a table. -/
noncomputable def upper (q : Nat → Nat → Nat → Nat → Nat × Nat) (k s : Nat) : Nat × Nat :=
  cond (Nat.beq s 0) (q (pt k) (co k) (pt k) (co k))
    (zadd (q (pt k) (co k) (pt (Nat.add k s)) (co (Nat.add k s)))
      (q (pt (Nat.add k s)) (co (Nat.add k s)) (pt k) (co k)))

/-- The matrix `rows` of E2 has the order 33, its upper triangle is that of the table `q`, and the checker of E2
accepts it. -/
noncomputable def matOk (q : Nat → Nat → Nat → Nat → Nat × Nat) (P : PSD.Params) (rows cols : Nat) : Bool :=
  Nat.beq P.n 33 && PSD.check P rows cols
    && N14.Local.triAll P.w 33 rows fun k s e => zeq (e, Nat.pow 2 (Nat.pred P.a)) (upper q k s)

noncomputable def hessOk (D : Dat) (kap K : Nat) (P : PSD.Params) (rows cols : Nat) : Bool :=
  matOk (qtab D kap K) P rows cols

noncomputable def rigOk (D : Dat) (sig K : Nat) (P : PSD.Params) (rows cols : Nat) : Bool :=
  matOk (rtab D sig K) P rows cols

/-! ## The cubic form -/

/-- The table of `<u_i, p_j - t p_i>`, scale `2^180`: zero outside the point `i`. -/
noncomputable def Mb (D : Dat) (T : Nat × Nat) (i j u c : Nat) : Nat × Nat :=
  ind (Nat.beq u i) (zsub (znat (Nat.shiftLeft 1 120) (gp D j c)) (zmul T (gp D i c)))

noncomputable def Lb (D : Dat) (T : Nat × Nat) (i j u c : Nat) : Nat × Nat :=
  zadd (Mb D T i j u c) (Mb D T j i u c)

/-- The table of `u_iᵀ (1 - p_i p_iᵀ) u_i`, scale `2^120`. -/
noncomputable def Gt (D : Dat) (i u c u' c' : Nat) : Nat × Nat :=
  ind (Nat.beq u i && Nat.beq u' i)
    (zsub (ind (Nat.beq c c') (Nat.shiftLeft 1 120, 0)) (zmul (gp D i c) (gp D i c')))

/-- The table of `u_iᵀ (1 - p_i p_iᵀ) (1 - p_j p_jᵀ) u_j`, scale `2^240`. -/
noncomputable def Ht (D : Dat) (T : Nat × Nat) (i j u c u' c' : Nat) : Nat × Nat :=
  ind (Nat.beq u i && Nat.beq u' j)
    (zadd
      (zsub (ind (Nat.beq c c') (Nat.shiftLeft 1 240, 0))
        (znat (Nat.shiftLeft 1 120) (zadd (zmul (gp D i c) (gp D i c')) (zmul (gp D j c) (gp D j c')))))
      (zmul T (zmul (gp D i c) (gp D j c'))))

/-- Twice the table of `psi_ij` with the projections, scale `2^240`. -/
noncomputable def psib2 (D : Dat) (T : Nat × Nat) (i j u c u' c' : Nat) : Nat × Nat :=
  zsub (znat 2 (Ht D T i j u c u' c')) (zmul T (zadd (Gt D i u c u' c') (Gt D j u c u' c')))

/-- The raw table of the cubic form of the pair `(i, j)` at the flat indices `k, a, b`, scale `2^600`. -/
noncomputable def Rraw (D : Dat) (T : Nat × Nat) (i j k a b : Nat) : Nat × Nat :=
  zsub
    (zadd
      (znat (gc D i j)
        (zmul (Lb D T i j (pt k) (co k)) (zmul (Lb D T i j (pt a) (co a)) (Lb D T i j (pt b) (co b)))))
      (znat (Nat.mul (Nat.shiftLeft 1 120) (gb D i j))
        (zmul (Lb D T i j (pt k) (co k)) (psib2 D T i j (pt a) (co a) (pt b) (co b)))))
    (znat (Nat.mul (Nat.shiftLeft 1 239) (ga D i j))
      (zadd (zmul (Mb D T i j (pt k) (co k)) (Gt D j (pt a) (co a) (pt b) (co b)))
        (zmul (Mb D T j i (pt k) (co k)) (Gt D i (pt a) (co a) (pt b) (co b)))))

/-- The sum of the raw table over the six orders of the indices. -/
noncomputable def R6 (D : Dat) (T : Nat × Nat) (i j k a b : Nat) : Nat × Nat :=
  zadd
    (zadd (zadd (Rraw D T i j k a b) (Rraw D T i j k b a)) (zadd (Rraw D T i j a k b) (Rraw D T i j a b k)))
    (zadd (Rraw D T i j b k a) (Rraw D T i j b a k))

/-- The point `u` is one of the points `i`, `j`. -/
noncomputable def inP (i j u : Nat) : Bool := Nat.beq u i || Nat.beq u j

/-- Six times the symmetric tensor of the cubic form, scale `2^600`. -/
noncomputable def T6 (D : Dat) (k a b : Nat) : Nat × Nat :=
  zsumP fun i j => ind (inP i j (pt k) && inP i j (pt a) && inP i j (pt b))
    (Prod.rec (motive := fun _ => Nat × Nat) (fun t1 t2 => R6 D (t1, t2) i j k a b) (tI D i j))

/-- The block `a` of the table holds the numbers `T6 k a b + off`. -/
noncomputable def tabOk (D : Dat) (off : Nat) (blk : List (List Nat)) (a : Nat) : Bool :=
  ball (fun b => ball (fun k => zeq (getN (getLN blk b) k, off) (T6 D k a b)) 33) 33

/-- `∑ (x - off) (y - off)` over the entries of two rows, in step. -/
noncomputable def dotR (off : Nat) : List Nat → List Nat → Nat × Nat :=
  List.rec (motive := fun _ => List Nat → Nat × Nat) (fun _ => (0, 0))
    (fun x _ ih ys => List.rec (motive := fun _ => Nat × Nat) (0, 0)
      (fun y ys' _ => zadd (zmul (x, off) (y, off)) (ih ys')) ys)

/-- The sum of `dotR` over the rows of two blocks, in step. -/
noncomputable def dotB (off : Nat) : List (List Nat) → List (List Nat) → Nat × Nat :=
  List.rec (motive := fun _ => List (List Nat) → Nat × Nat) (fun _ => (0, 0))
    (fun r _ ih bs => List.rec (motive := fun _ => Nat × Nat) (0, 0)
      (fun s bs' _ => zadd (dotR off r s) (ih bs')) bs)

/-- `∑_{b, k} (tab a b k - off) (tab a' b k - off)`: the Gram matrix of the blocks of the table. -/
noncomputable def wEnt (off : Nat) (tab : List (List (List Nat))) (a a' : Nat) : Nat × Nat :=
  dotB off (getLLN tab a) (getLLN tab a')

noncomputable def lenN : List Nat → Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih)

noncomputable def lenLN : List (List Nat) → Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih)

/-- The table has 33 blocks of 33 rows with 33 entries. -/
noncomputable def shapeOk (tab : List (List (List Nat))) : Bool :=
  ball (fun a => Nat.beq (lenLN (getLLN tab a)) 33
    && ball (fun b => Nat.beq (lenN (getLN (getLLN tab a) b)) 33) 33) 33

/-- The upper triangle of `c3s [a = a'] - W`. -/
noncomputable def wUpper (off c3s : Nat) (tab : List (List (List Nat))) (k s : Nat) : Nat × Nat :=
  cond (Nat.beq s 0) (zsub (c3s, 0) (wEnt off tab k k)) (znat 2 (zneg (wEnt off tab k (Nat.add k s))))

/-- The number of slots before the row `k` of a triangular array of order 33. -/
noncomputable def toff (k : Nat) : Nat := Nat.sub (Nat.mul k 33) (Nat.div (Nat.mul k (Nat.pred k)) 2)

/-- The entry `(k, k + s)` of the matrix `rows` of E2 is that of `c3s [a = a'] - W`. One theorem holds one
entry: the time of a kernel evaluation grows faster than the number of the entries that it contains. -/
noncomputable def wEntOk (off c3s : Nat) (tab : List (List (List Nat))) (P : PSD.Params) (rows k s : Nat) : Bool :=
  zeq (slot P.w rows (Nat.add (toff k) s), Nat.pow 2 (Nat.pred P.a)) (wUpper off c3s tab k s)

/-- The table has its shape, the matrix `rows` has the order 33, and the checker of E2 accepts it. -/
noncomputable def cubOk (tab : List (List (List Nat))) (P : PSD.Params) (rows cols : Nat) : Bool :=
  Nat.beq P.n 33 && shapeOk tab && PSD.check P rows cols

/-! ## The coefficients, the residual, the sums -/

/-- The tests of the enclosures with `Q = q`: `(A ∓ E)² q³ ≶ 2^480`, `(2 B ∓ 3 E)² q⁵ ≶ 9 * 2^720`,
`(2 C ∓ 5 E)² q⁷ ≶ 25 * 2^960`. -/
noncomputable def encQ (A B C E q : Nat) : Bool :=
  forceN false (Nat.mul q (Nat.mul q q)) fun q3 => forceN false (Nat.mul q3 (Nat.mul q q)) fun q5 =>
  forceN false (Nat.mul q5 (Nat.mul q q)) fun q7 =>
    Nat.blt E A
    && Nat.ble (Nat.mul (Nat.pow (Nat.sub A E) 2) q3) (Nat.shiftLeft 1 480)
    && Nat.ble (Nat.shiftLeft 1 480) (Nat.mul (Nat.pow (Nat.add A E) 2) q3)
    && Nat.blt (Nat.mul 3 E) (Nat.mul 2 B)
    && Nat.ble (Nat.mul (Nat.pow (Nat.sub (Nat.mul 2 B) (Nat.mul 3 E)) 2) q5) (Nat.shiftLeft 9 720)
    && Nat.ble (Nat.shiftLeft 9 720) (Nat.mul (Nat.pow (Nat.add (Nat.mul 2 B) (Nat.mul 3 E)) 2) q5)
    && Nat.blt (Nat.mul 5 E) (Nat.mul 2 C)
    && Nat.ble (Nat.mul (Nat.pow (Nat.sub (Nat.mul 2 C) (Nat.mul 5 E)) 2) q7) (Nat.shiftLeft 25 960)
    && Nat.ble (Nat.shiftLeft 25 960) (Nat.mul (Nat.pow (Nat.add (Nat.mul 2 C) (Nat.mul 5 E)) 2) q7)

/-- The tests of the enclosures for `<P_i, P_j> = t1 - t2`: `Q = 2^121 - 2 (t1 - t2)` is positive, and `encQ`. -/
noncomputable def encBody (A B C E t1 t2 : Nat) : Bool :=
  Nat.blt (Nat.mul 2 t1) (Nat.add (Nat.shiftLeft 1 121) (Nat.mul 2 t2))
    && forceN false (Nat.sub (Nat.add (Nat.shiftLeft 1 121) (Nat.mul 2 t2)) (Nat.mul 2 t1)) fun q => encQ A B C E q

/-- The enclosures of the coefficients of the pair `(i, j)`: with `Q = 2^121 - 2 T`,
`(A ∓ E)² Q³ ≶ 2^480`, `(2 B ∓ 3 E)² Q⁵ ≶ 9 * 2^720`, `(2 C ∓ 5 E)² Q⁷ ≶ 25 * 2^960`. -/
noncomputable def encPair (D : Dat) (E i j : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun t1 t2 => encBody (ga D i j) (gb D i j) (gc D i j) E t1 t2) (tI D i j)

noncomputable def encOk (D : Dat) (E : Nat) : Bool :=
  ball (fun j => ball (fun i => encPair D E i j) j) 11

/-- The tables of the coefficients are symmetric. -/
noncomputable def symOk (D : Dat) : Bool :=
  ball (fun j => ball (fun i =>
    Nat.beq (ga D i j) (ga D j i) && Nat.beq (gb D i j) (gb D j i) && Nat.beq (gc D i j) (gc D j i)) j) 11

/-- `F_i = ∑_{j ≠ i} A_ij P_j`, scale `2^120`. -/
noncomputable def fI (D : Dat) (i c : Nat) : Nat × Nat :=
  zsum (fun j => ind (not (Nat.beq j i)) (znat (ga D i j) (gp D j c))) 11

/-- `mu_i = <F_i, P_i>`, scale `2^180`. -/
noncomputable def muI (D : Dat) (i : Nat) : Nat × Nat :=
  zadd (zadd (zmul (fI D i 0) (gp D i 0)) (zmul (fI D i 1) (gp D i 1))) (zmul (fI D i 2) (gp D i 2))

/-- `2^120 F_i - mu_i P_i`, scale `2^240`. -/
noncomputable def gI (D : Dat) (i c : Nat) : Nat × Nat :=
  zsub (znat (Nat.shiftLeft 1 120) (fI D i c)) (zmul (muI D i) (gp D i c))

/-- The residual of the first-order condition: `∑ |g_i|² ≤ Gam²`, scale `2^480`. -/
noncomputable def gradOk (D : Dat) (Gam : Nat) : Bool :=
  zle (zsum (fun i => zsum (fun c => zmul (gI D i c) (gI D i c)) 3) 11) (Nat.mul Gam Gam, 0)

/-- The sums of the coefficients over the pairs that contain a point. -/
noncomputable def rowsOk (D : Dat) (Ra Rb Rc : Nat) : Bool :=
  ball (fun i =>
    Nat.ble (nsum (fun j => cond (Nat.beq j i) 0 (ga D i j)) 11) Ra
    && Nat.ble (nsum (fun j => cond (Nat.beq j i) 0 (gb D i j)) 11) Rb
    && Nat.ble (nsum (fun j => cond (Nat.beq j i) 0 (gc D i j)) 11) Rc) 11

/-- `| |P_i|² - 2^120 | ≤ e`. -/
noncomputable def normOk (D : Dat) (e : Nat) : Bool :=
  ball (fun i => zle (tI D i i) (Nat.add (Nat.shiftLeft 1 120) e, 0)
    && zle (Nat.shiftLeft 1 120, e) (tI D i i)) 11

/-- `<P_i, P_j> ≤ tmax` for `i < j`. -/
noncomputable def topOk (D : Dat) (tmax : Nat) : Bool :=
  ball (fun j => ball (fun i => zle (tI D i j) (tmax, 0)) j) 11

end N11.Local
