# AnalyticArguments

The arguments of the proof.

| File | Contents |
| --- | --- |
| [analytic_arguments.pdf](analytic_arguments.pdf), [analytic_arguments.tex](analytic_arguments.tex) | The proof in the form that Lean verifies: the theorem, the statements that Lean takes from the certificates, and the analytic arguments that lead from these statements to the theorem, with the names of their Lean theorems. |

The proof has a computational part and an analytic part.

* Sections 2 and 3 state the seven statements (G1) to (G7) of the computational part and the two
  theorems that collect them. Each statement is established by the certificates of
  [Certificates](../Certificates).
* Section 4 contains the analytic arguments: a minimizer exists and is a critical point; a
  configuration is aligned with a reference configuration by an orthogonal transformation; the
  inner products of a configuration determine its distance from the reference configuration; the
  energy grows quadratically near the reference configuration; the minimizer is unique. The Lean
  files are those of [LeanCode/N11/Analytic](../LeanCode/N11/Analytic).
* Section 5 lists the parts of the proof in Lean.
