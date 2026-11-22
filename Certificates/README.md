# Certificates

The computational part of the proof consists of seven statements, (G1) to (G7); they are stated in
[AnalyticArguments/analytic_arguments.pdf](../AnalyticArguments/analytic_arguments.pdf), Sections 2 and 3.
Each of them is established by certificates: exact data on which the Lean kernel evaluates a checker.
The checkers and the theorems that derive a mathematical statement from an accepted check are in
[LeanCode](../LeanCode). This folder holds the data: 5,914 generated Lean modules.

| Folder | Statement | Modules | Main theorems |
| --- | --- | ---: | --- |
| [G1_UpperBound](G1_UpperBound) | (G1): an explicit rational configuration is separated and has energy at most $\tilde E = 40.59645051$ | 2 | `N11U.sep`, `N11U.energy_le` |
| [G2_LinearProgramming](G2_LinearProgramming) | (G2): a configuration with energy at most $\tilde E$ has all inner products below $73/100$ | 2 | `N11LP.top` |
| [G3_Exclusions](G3_Exclusions) | (G3): 5,215 patterns on 7 to 11 vertices do not occur in a configuration with energy at most $\tilde E$ (folders `X07` to `X11`) | 5,322 | `N11G.<certificate>.excl` |
| [G4_Enumeration](G4_Enumeration) | (G4): the points of such a configuration have one of three patterns on eleven vertices | 55 | `N11E.enum` |
| [G5_Cells](G5_Cells) | (G5): the cells of the three patterns outside a box around the minimizer have energy above $\tilde E$ | 491 | `N11C.star`, `N11C.saddleA`, `N11C.saddleB`, `N11C.shell` |
| [G6_InnerBox](G6_InnerBox) | (G6): inside the box the energy minus a quadratic penalty exceeds $\tilde E - 10^{-6}$ | 3 | `N11G.IN_c2_d100_D6_c0090.conf` |
| [G7_LocalConstants](G7_LocalConstants) | (G7): bounds for a polynomial below the energy at a reference configuration | 37 | `N11L.g7`, `N11L.link_0` |
| [Route](Route) | (G1) to (G6) as one theorem about configurations of eleven points | 1 | `N11RG.routeG`, `N11RG.nonempty` |
| [Theorem](Theorem) | the hypotheses of the analytic part, and the theorem in coordinates | 1 | `N11.T6A.thomson11` |

## Data modules and statement modules

A **data module** contains natural numbers in hexadecimal notation (`hex% "…"`), a few definitions that
arrange them, and theorems of the form `check data = true := by decide +kernel`: the Lean kernel evaluates
the checker on the data. There are 5,767 data modules with 13.2 GB of source. They are stored compressed, as
`<name>.lean.xz` (3.7 GB in total).

A **statement module** applies the soundness theorems of the library to the checks of data modules and
obtains statements about configurations of points. It ends with a test that its theorems depend on the
axioms `propext`, `Classical.choice` and `Quot.sound` only (`#guard_msgs in #print axioms …`). The 147
statement modules are stored as they are; they are the files to read. Start with
[Route/N11RG.lean](Route/N11RG.lean) and [Theorem/T6A.lean](Theorem/T6A.lean).

Every Lean file below this folder is a module of the Lake library `Certificates`; the module
`Certificates.G3_Exclusions.X07.SX07_0000` is the file `G3_Exclusions/X07/SX07_0000.lean`. The header of a
module names the program that wrote it. These programs are not part of this repository, and nothing in the
verification depends on them: Lean checks the modules as they are.

## Unpacking

Lean needs the data modules as `.lean` files. From the root of the repository:

```sh
python3 Certificates/unpack.py
```

This writes `<name>.lean` next to every `<name>.lean.xz` (13.2 GB) and then compares all 5,914 modules with
[MANIFEST.sha256](MANIFEST.sha256), which lists the SHA-256 of every module in its unpacked form. The
program needs Python 3 only. Without Python the same is done by

```sh
find Certificates -name '*.lean.xz' -exec xz -dk {} +
```

and, on Linux, the comparison by `cd Certificates && sha256sum --quiet -c MANIFEST.sha256`.
`python3 Certificates/unpack.py --clean` removes the unpacked files again.
