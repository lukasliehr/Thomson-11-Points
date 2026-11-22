module

public import N11.ParallelResearch1.Circ.GraphKernel

/-!
# The enumeration of contact graphs by adding a point: the check of a level (`Init` and kernel modules only)

A *table* of patterns is a natural number with 56 bits for every pattern (`tabAt`). A *map of vertices* is a
natural number with four bits for every vertex (`dig`).

`embOk m h n g s`: the map `s` embeds the pattern `h` on `m` vertices into the pattern `g` on `n` vertices: its values
on `0, …, m - 1` are below `n` and distinct, and a pair is an edge of `h` if and only if its image is an edge of `g`.

A level `k` has the table `F` of the patterns on `k` vertices that are kept, the table `F1` of those on `k + 1`
vertices, and for every size `m` a table `B m` of patterns on `m` vertices that are excluded (with `Bc m` entries).
For a pattern `g` of `F` and a set `S` of vertices below `k`, the *extension* is the pattern `g + S * 2 ^ pairs k`
on `k + 1` vertices: the new vertex `k` is joined to the vertices of `S`. A *row* of the level holds one entry of 64
bits for every `S < 2 ^ k`; the entry `e` is accepted (`entryOk`) if

* its bit 0 is `0`, the bits 1 to 4 hold `k + 1`, the bits 5 to 16 hold an index `j < c1`, and the map in the bits
  from 17 on embeds the pattern `j` of `F1` into the extension (so the extension is that pattern with other labels),
  or
* its bit 0 is `1`, the bits 1 to 4 hold a size `m`, the bits 5 to 16 an index `j < Bc m`, and the map embeds the
  pattern `j` of `B m` into the extension (so the extension contains an excluded pattern).

`rowsOk`: the rows `i, i + 1, …` of a list are accepted for the patterns `i, i + 1, …` of `F`. The checks are
bit-exact with `cert/enumref.py`; their use is `N11.Circ.step` (`Enum.lean`).
-/

@[expose] public section

namespace N11.Circ

open CAP CAP.Wsos

/-- The entry `j` of a table of patterns: 56 bits each. -/
noncomputable def tabAt (T j : Nat) : Nat := Nat.land (Nat.shiftRight T (Nat.mul 56 j)) 72057594037927935

/-- The value at `a` of a map of vertices: four bits each. -/
noncomputable def dig (s a : Nat) : Nat := Nat.land (Nat.shiftRight s (Nat.mul 4 a)) 15

/-- The two truth values agree. -/
noncomputable def sameB (a b : Bool) : Bool := cond a b (cond b false true)

/-- `f v`, with the value `v` computed first: the kernel reduces the major premise `v + 1` of the recursor to a
numeral and passes the numeral `v` to `f`. Without it a value that is used in a loop is computed at every use. -/
noncomputable def strict (v : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun n _ => f n) (Nat.add v 1)

/-- The map `s` embeds the pattern `h` on `m` vertices into the pattern `g` on `n` vertices. -/
noncomputable def embOk (m h n g s : Nat) : Bool :=
  allN (fun b => strict (dig s b) fun sb => strict (pairs b) fun pb => Nat.blt sb n
    && allN (fun a => strict (dig s a) fun sa =>
        cond (Nat.beq sa sb) false (sameB (tbit h (Nat.add pb a)) (adjG g sa sb))) b) m

/-- The size, the index and the map of an entry. -/
noncomputable def entM (e : Nat) : Nat := Nat.land (Nat.shiftRight e 1) 15

noncomputable def entJ (e : Nat) : Nat := Nat.land (Nat.shiftRight e 5) 4095

noncomputable def entS (e : Nat) : Nat := Nat.shiftRight e 17

/-- The entry `e` is accepted for the pattern `g` on `n` vertices. -/
noncomputable def entryOk (n g F1 c1 : Nat) (B Bc : List Nat) (e : Nat) : Bool :=
  strict (entM e) fun m => strict (entJ e) fun j => strict (entS e) fun s =>
    cond (Nat.beq (Nat.land e 1) 0)
      (Nat.beq m n && Nat.blt j c1 && strict (tabAt F1 j) fun h => embOk n h n g s)
      (Nat.blt j (nth Bc m) && strict (tabAt (nth B m) j) fun h => embOk m h n g s)

/-- The row of the pattern `g` on `k` vertices is accepted. -/
noncomputable def rowOk (k g F1 c1 : Nat) (B Bc : List Nat) (row : Nat) : Bool :=
  strict (Nat.pow 2 (pairs k)) fun pk => Nat.blt g pk
    && allN (fun S => strict (Nat.add g (Nat.mul S pk)) fun g' =>
        strict (Nat.land (Nat.shiftRight row (Nat.mul 64 S)) 18446744073709551615) fun e =>
          entryOk (Nat.succ k) g' F1 c1 B Bc e) (Nat.pow 2 k)

/-- The rows of a list are accepted for the patterns `i, i + 1, …` of the table `F`. -/
noncomputable def rowsOk (k F F1 c1 : Nat) (B Bc : List Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun row _ ih i => (strict (tabAt F i) fun g => rowOk k g F1 c1 B Bc row) && ih (Nat.succ i))

end N11.Circ
