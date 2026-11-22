module

public import CAP.Wsos.Kernel

/-!
# The data of a typed certificate, and the triple types that they define (`Init` only)

A typed three-point certificate divides the points into classes `0, …, q - 1`. Its data belong to
classes (the number of points, the Gram matrices of the rooted blocks), to pairs of classes `a ≤ b`
(the box of the inner product, the pair polynomial `H`), and to a pair with a third class (the share
of the pair that belongs to the points of the third class). For every pair one share is not given:
the share of the class `last a b`, which the share equation determines.

`tyOf C X` is the record of a triple type that the checker `checkTy` reads: its boxes, shares and
rooted blocks are those of the certificate `C`, and `X` holds the data of the triple type alone (the
weights, the constant and the Chebyshev numbers). Hence two triple types of a certificate use the
same pair polynomials, shares and rooted blocks by construction, which the theorem of the schema
needs.

`Cert.ofLists` builds a certificate from tables; the generated modules use it.

The file also contains the sorted triple of three classes (`lo3`, `mid3`, `hi3`, `typeOf`), the numbers
of pairs and triples of points with given classes (`pcnt`, `cnt`), and the multiplicities of the shares
of a triple type (`smult`, `tmult`), which the checks of `CertKernel.lean` use.
-/

@[expose] public section

namespace CAP.Wsos

/-- The data of a typed certificate that do not belong to a single triple type. Pairs are `a ≤ b`. -/
structure Cert where
  /-- the number of points of a class -/
  n : Nat → Nat
  /-- the box of the inner products of a pair type -/
  box : Nat → Nat → Box
  /-- the pair polynomial of a pair type: packed signed digits of `P.wP` bits, scaled by `2 ^ sP` -/
  H : Nat → Nat → Nat
  /-- the share of a pair type for a third class, in the same form -/
  p : Nat → Nat → Nat → Nat
  /-- the Gram matrices of the rooted blocks of a class -/
  gram : Nat → List Nat
  /-- the third class of a pair type whose share is given by the share equation -/
  last : Nat → Nat → Nat

/-- The number of points of the class `x` besides one point of the class `a` and one of the class `b`. -/
def mult (C : Cert) (a b x : Nat) : Nat :=
  Nat.sub (Nat.sub (C.n x) (cond (Nat.beq x a) 1 0)) (cond (Nat.beq x b) 1 0)

noncomputable def tabGo (f : Nat → Nat) : Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc) (fun k ih acc => ih (f k :: acc))

/-- `[f 0, …, f (n - 1)]` -/
noncomputable def tab (f : Nat → Nat) (n : Nat) : List Nat := tabGo f n []

/-- The share of the pair type `(a, b)` for the third class `c`. For `c = last a b` it is the share of
the share equation: `mult` times this share is `H` minus the shares of the classes below `c`, each
with its multiplicity, minus the rooted forms of the two classes at coinciding points. -/
noncomputable def shareOf (C : Cert) (a b c : Nat) : Share :=
  cond (Nat.beq c (C.last a b))
    ⟨mult C a b c, C.H a b, tab (C.p a b) c, tab (mult C a b) c, [⟨C.gram a, a, b⟩, ⟨C.gram b, b, a⟩]⟩
    ⟨1, C.p a b c, [], [], []⟩

/-- The data of a triple type `a ≤ b ≤ c` that belong to it alone. -/
structure TyX where
  a : Nat
  b : Nat
  c : Nat
  weights : List Weight
  /-- the constant, as a difference -/
  c2p : Nat
  c2n : Nat
  /-- the Chebyshev numbers, as a difference -/
  Np : Nat
  Nn : Nat

/-- The record of the triple type for the checker. -/
noncomputable def tyOf (C : Cert) (X : TyX) : Ty :=
  ⟨C.box X.a X.b, C.box X.a X.c, C.box X.b X.c, shareOf C X.a X.b X.c, shareOf C X.a X.c X.b,
    shareOf C X.b X.c X.a, ⟨C.gram X.a, X.b, X.c⟩, ⟨C.gram X.b, X.a, X.c⟩, ⟨C.gram X.c, X.a, X.b⟩,
    X.weights, X.c2p, X.c2n, X.Np, X.Nn⟩

/-- Does the entry belong to the triple type `(a, b, c)`? -/
def isKey (a b c : Nat) (X : TyX) : Bool := Nat.beq X.a a && Nat.beq X.b b && Nat.beq X.c c

/-- The first entry of a list for the triple type `(a, b, c)`. -/
noncomputable def findX (a b c : Nat) : List TyX → TyX :=
  List.rec ⟨0, 0, 0, [], 0, 0, 0, 0⟩ (fun X _ ih => cond (isKey a b c X) X ih)

/-- Is there an entry for the triple type `(a, b, c)`? -/
noncomputable def hasX (a b c : Nat) : List TyX → Bool :=
  List.rec false (fun X _ ih => cond (isKey a b c X) true ih)

/-! ## Sorted triples of classes, and the numbers of pairs and triples of points -/

def min2 (a b : Nat) : Nat := cond (Nat.ble a b) a b

def max2 (a b : Nat) : Nat := cond (Nat.ble a b) b a

/-- The smallest, the middle and the largest of three numbers. -/
def lo3 (a b c : Nat) : Nat := min2 a (min2 b c)

def hi3 (a b c : Nat) : Nat := max2 a (max2 b c)

def mid3 (a b c : Nat) : Nat := Nat.sub (Nat.sub (Nat.add (Nat.add a b) c) (lo3 a b c)) (hi3 a b c)

/-- The entry of a list for the triple type of three classes in any order. -/
noncomputable def typeOf (xs : List TyX) (a b c : Nat) : TyX := findX (lo3 a b c) (mid3 a b c) (hi3 a b c) xs

/-- The number of pairs of distinct points with the classes `a` and `b`, in this order. -/
def pcnt (C : Cert) (a b : Nat) : Nat := Nat.mul (C.n a) (Nat.sub (C.n b) (cond (Nat.beq b a) 1 0))

/-- The number of triples of distinct points with the classes `a`, `b`, `c`, in this order. -/
def cnt (C : Cert) (a b c : Nat) : Nat := Nat.mul (pcnt C a b) (mult C a b c)

/-- The multiplicity of the share of the pair type `(a, b)` for the class `c` in the record of a triple type. -/
def smult (C : Cert) (a b c : Nat) : Nat := cond (Nat.beq c (C.last a b)) (mult C a b c) 1

/-- The product of the multiplicities of the three shares of a triple type. -/
def tmult (C : Cert) (X : TyX) : Nat :=
  Nat.mul (Nat.mul (smult C X.a X.b X.c) (smult C X.a X.c X.b)) (smult C X.b X.c X.a)

/-! ## Tables -/

noncomputable def nthB : List Box → Nat → Box :=
  List.rec (motive := fun _ => Nat → Box) (fun _ => ⟨0, 0, 0⟩)
    (fun h _ ih i => Nat.rec (motive := fun _ => Box) h (fun j _ => ih j) i)

noncomputable def nthL : List (List Nat) → Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun h _ ih i => Nat.rec (motive := fun _ => List Nat) h (fun j _ => ih j) i)

/-- A certificate from tables: the entry of the pair `(a, b)` has the index `a * q + b`, the entry of
the pair `(a, b)` with the third class `c` the index `(a * q + b) * q + c`. -/
noncomputable def Cert.ofLists (q : Nat) (n : List Nat) (box : List Box) (H p : List Nat) (gram : List (List Nat))
    (last : List Nat) : Cert :=
  ⟨nth n, fun a b => nthB box (Nat.add (Nat.mul a q) b), fun a b => nth H (Nat.add (Nat.mul a q) b),
    fun a b c => nth p (Nat.add (Nat.mul (Nat.add (Nat.mul a q) b) q) c), nthL gram,
    fun a b => nth last (Nat.add (Nat.mul a q) b)⟩

end CAP.Wsos
