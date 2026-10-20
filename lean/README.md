# Jensen–Toft 9.13: the power-of-two family

Alex Chan — Harvard University and National Bureau of Economic Research

For k = 2^r, r >= 1:
chi(K(2k,k,k-1)) = binomial(2k,k)/(k+1).

Lean 4.34.0 and mathlib v4.34.0 verify this formula.
The final theorem is JT913.conventionalTheorem_verified.
The source is lean/JT913.lean; the audit is lean/Audit.lean.
Exact dependencies are recorded in lean/lake-manifest.json.

Verified components include the XOR coloring, its fibers and sizes,
the exact color count, the independent-set bound, and relabeling.
The final theorem depends only on propext, Classical.choice, Quot.sound.

Section 3's supplementary constant-weight-code properties and the
explicit Johnson-graph clique-cover formulation are not separately
formalized. The result does not settle unrestricted Jensen–Toft 9.13.

To check the proof, enter the lean directory and run:
    lake exe cache get
    lake build
    lake env lean Audit.lean

The paper's TeX and PDF are in paper/.
The Python generator, finite witness, and tests are in graph_code/.
The files in notes/ record the initial mathematical review.
