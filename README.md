# Zhang’s affine-line weight bound in Lean 4

Let $k=\mathbf F_q$ and let $E$ be a lisse $\overline{\mathbf Q}_\ell$-sheaf on $\mathbf A^1_k$, with $\ell\nmid q$. Fix an embedding $\iota$ into $\mathbf C$. If the stalks of $E$ have pointwise weights at most $w$, every eigenvalue $\alpha$ of geometric Frobenius on $H_c^1(\mathbf A^1_{\bar k},E)$ satisfies

$$
|\iota(\alpha)|\le q^{(w+1)/2}.
$$

This is Theorem 1.1 of Dingxin Zhang’s *On an Elementary Proof of Weil II*. The Lean development follows the paper from a finite-field exponential sum to a bound on all Frobenius power traces. A tensor-power argument then gives the sharp exponent above. [Paper, pp. 1–5](https://arxiv.org/pdf/2611.30749v1) · [Main theorem in Lean](WeilII/Targets/AffineLineWeightBound.lean)

| To find | Read |
| --- | --- |
| The hypotheses, conventions and exact Lean declarations for all seven results | [Mathematical statements](docs/mathematics.md) |
| How one smooth chain section gives the weight bound, and where general weak Lefschetz enters the geometry | [Proof guide](docs/proof-guide.md) |
| How to follow a declaration to its dependencies and check the excluded weight estimates | [Reading a proof trace](docs/proof-guide.md#reading-a-proof-trace) · [Trace index](traces/index.json) |
| The comparison with the pinned upstream development and the resources used | [Project report](docs/project-report.md) · [Module inventory](docs/module-inventory.tsv) |

## Build and inspect the main theorem

From the repository root, with Git and the Lean toolchain manager `elan` installed, run

```sh
lake build
```

Lake reads the default library target `WeilII`. Its module glob includes the seven target modules. The toolchain is Lean 4.35.0. The manifest fixes `weil-conjectures` at `497f33d964609973fe4ed9647a1e5d32369f0d09` and Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679`. A clean checkout needs network access for the pinned toolchain and packages. [Toolchain](lean-toolchain) · [Lake configuration](lakefile.toml) · [Dependency manifest](lake-manifest.json)

To ask Lean for the full type and the axioms used by its proof, run this after the build. Each entry in the mathematical statements links to the source file for the corresponding import.

```sh
lake env lean --stdin <<'LEAN'
import WeilII.Targets.AffineLineWeightBound
#check WeilII.affineLine_h1c_hasWeightsAtMost
#print axioms WeilII.affineLine_h1c_hasWeightsAtMost
LEAN
```

The allowed axioms are `propext`, `Classical.choice` and `Quot.sound`. A separate dependency check follows the constants in elaborated types and proof terms to identify any use of earlier Weil II weight estimates. The index records the frozen source and upstream revisions, each target’s declaration and allowed axioms, and the digest of each module’s trace. [Trace index](traces/index.json) · [Excluded declarations](traces/excluded-declarations.txt)

## Independent acceptance

All seven results passed independent acceptance against the reviewed statements. For Proposition 1.5, Lemmas 2.1, 2.2 and 2.6, Theorem 2.4 and Construction 2.5, the official comparator checked the statement and permitted axioms, and the default Lean kernel accepted the solution. For Theorem 1.1 the official comparator checked the statement and permitted axioms, and 16-thread NanoDa checked the same final solution export. It checked 297,335 declarations with zero typechecking errors and one diagnostic while printing the axiom list. The target entries record both the comparator scope and the proof checker. [Acceptance index](traces/index.json) · [Costs and export fingerprints](docs/project-report.md)

On the punctually pure case common to both proofs, the new route avoids 51,700 upstream lines and uses 25,476 exclusive lines of its own or from other upstream declarations. The difference is 26,224 mapped lines out of 1,489,542. The comparison includes shared dependencies and gives separate counts for all seven project targets. [Scope of the comparison](docs/upstream-replacement.md) · [Recount from source](docs/recount.md) · [Resource ledger](docs/resources.tsv)
