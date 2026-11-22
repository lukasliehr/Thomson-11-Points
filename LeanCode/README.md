# LeanCode

The Lean code of the verification: the statement, the checkers with their soundness theorems, and
the analytic part of the proof. The certificates on which the checkers run are the Lean modules of
[Certificates](../Certificates). The folder is the source directory of four Lake libraries; the
module `N11.Analytic.Main` is the file `N11/Analytic/Main.lean`. It contains 104 files with 26,030
lines.

| Path | Contents |
| --- | --- |
| [N11/Statement.lean](N11/Statement.lean) | The theorem in coordinates, as the proposition `N11.Thomson11`. It uses Mathlib only. |
| [N11/Analytic](N11/Analytic) | The analytic part: existence and criticality of a minimizer, the alignment, rigidity, the lower bound near the reference configuration, uniqueness, and the assembly `N11.thomson11_of`. |
| [N11/Local](N11/Local) | The local constants, statement (G7): the checks for the kernel and the theorem `N11.Local.g7_of` that derives the statement from them. |
| [N11/ParallelResearch1/Circ](N11/ParallelResearch1/Circ) | The statements (G1) to (G6): the typed three-point bound on the two-sphere with the kernels of the circle, patterns and exclusions, the enumeration, cells and covers, the upper bound of the energy, the bound by linear programming. Files named `…Kernel.lean` are the checkers that the Lean kernel evaluates; the other files prove their soundness. |
| [CAP](CAP) | Checkers and soundness theorems that are not specific to eleven points: packed arithmetic, positive definiteness, the sign of a polynomial on an interval, the three-point bound and its typed form. |
| [N14](N14) | Three files of checks that the local constants share with a verification for 14 points. |
| [CAPNumeral](CAPNumeral) | The notation `hex% "…"` for large natural numbers. It is an elaborator that Lake compiles to native code; it only produces `Nat` literals, and the kernel checks every statement about them. |

The proof of the theorem in coordinates is `N11.T6A.thomson11` in
[Certificates/Theorem/T6A.lean](../Certificates/Theorem/T6A.lean): it applies `N11.thomson11_of` to the
theorems of the certificates. [Showcase_WithProofs.lean](../Showcase_WithProofs.lean) passes from it to
points of the Euclidean space and to linear isometries.

A checker is a function with values in `Bool` that computes with natural numbers. A certificate is accepted
by a theorem `check data = true := by decide +kernel`, which the Lean kernel proves by evaluating the
checker; the soundness theorem of the checker turns this into a mathematical statement. No file uses
`native_decide`, `sorry` or an additional axiom.

## Names in the comments

The files were developed in a repository that contains the verification of several theorems, and
their comments use its names.

| Name | Meaning |
| --- | --- |
| `T6` | The theorem for 11 points. |
| route G, (G1) to (G7) | The proof by contact graphs of this repository and its seven computational statements; see [AnalyticArguments](../AnalyticArguments). |
| `E2`, `E11`, … | Kinds of checkers of the library, for example `E2` for positive semidefiniteness. |
| generated modules, `N11RG`, `N11L`, `T6A`, … | The modules of [Certificates](../Certificates). |
| `N11/README.md`, `caps/…`, `certgen/…`, the write-up, the source | Documents and programs of the development repository, which are not part of this repository. |

The files are those of the development repository, unchanged, with one exception: two sentences of
the comment at the head of [N11/Statement.lean](N11/Statement.lean) referred to documents that
are not part of this repository and were replaced.
