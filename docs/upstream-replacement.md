# Comparing Zhang’s proof with the Peking University development

On a punctually pure lisse sheaf on the whole affine line, Zhang’s proof of the degree-one weight bound uses **26,224 fewer mapped source lines** than the upstream degree-one proof. That is **1.76% of the upstream derivation’s 1,489,542 mapped lines**. The formalized Theorem 1.1 also treats sheaves for which only a pointwise upper bound is given. A comparison on that full domain would require an upstream proof under the same hypotheses. [Mathematical statements](mathematics.md) · [Module inventory](module-inventory.tsv)

## Theorem 1.1 on the common input

Fix a finite field of order $q$, a prime $\ell$ invertible in the field, an embedding $\iota$ of the coefficient field into $\mathbf C$, and a real number $w$. Let $E$ be a lisse adic sheaf on the whole arithmetic affine line, and $F$ its geometric pullback with its induced Weil structure. Assume that every stalk eigenvalue at each closed point $x$ has absolute value **equal to** $q_x^{w/2}$ under $\iota$. Both Lean witnesses conclude that every Frobenius eigenvalue on $H_c^1(\mathbf A^1_{\bar k},F)$ has absolute value at most $q^{(w+1)/2}$.

| Mapped physical lines | Upstream derivation | Zhang derivation |
| --- | ---: | ---: |
| Upstream source used by both | 1,437,842 | 1,437,842 |
| Upstream source exclusive to the upstream derivation | 51,700 | 0 |
| Upstream source exclusive to Zhang’s derivation | 0 | 7,507 |
| Project source exclusive to Zhang’s derivation | 0 | 17,969 |
| **Total** | **1,489,542** | **1,463,318** |

The upstream witness instantiates `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.hasWeightsAtMostOver_compactlySupportedCohomology_one_of_isPunctuallyPureOfWeight` with the entire line as its dense open, the identity immersion and $F$ as its sheaf. The project witness supplies `IsPunctuallyPureOfWeight.hasWeightsAtMost` to `WeilII.affineLine_h1c_hasWeightsAtMost`. The gross upstream footprint avoided is 51,700 / 1,489,542 = 3.47%. The signed saving after paying for 7,507 other upstream lines and 17,969 project lines is (51,700 − 7,507 − 17,969) / 1,489,542 = +1.76%. [Upstream degree-one proof](https://github.com/formal-arithmetic-geometry/weil-conjectures/blob/497f33d964609973fe4ed9647a1e5d32369f0d09/WeilConjectures/DeligneLaumon/AffineLine/AffineCurveUpper.lean#L341) · [Zhang’s degree-one proof](../WeilII/Targets/AffineLineWeightBound.lean)

The full Theorem 1.1 assumes the pointwise inequality $|\iota(\gamma)|\le q_x^{w/2}$. For example, the rank-one constant sheaf satisfies that bound at $w=1$ with strict inequality. An upstream mixed-sheaf estimate gives another route *if* a mixed filtration is supplied. No checked construction of that filtration from the pointwise bound alone was identified. Upstream also proves results for a lisse sheaf on a proper dense open, constructible sheaves and other cohomological degrees. These additional hypotheses and conclusions determine which calls the project can replace. [Upstream weight predicates](https://github.com/formal-arithmetic-geometry/weil-conjectures/blob/497f33d964609973fe4ed9647a1e5d32369f0d09/WeilConjectures/WeilSheaf/Stalk.lean#L327) · [Mixed cohomology bound](https://github.com/formal-arithmetic-geometry/weil-conjectures/blob/497f33d964609973fe4ed9647a1e5d32369f0d09/WeilConjectures/ZetaFunction/LissePurity.lean#L56)

## Seven targets and the scope of the comparison

The project counts start at the following seven declarations, each in the `WeilII` namespace. The union includes each declaration once and each source line once per file, even when several target proofs reach it. For example, the proof of 1.1 reaches 1.5 and the three lemmas 2.1, 2.2 and 2.6. General Theorem 2.4 and Construction 2.5 share geometric inputs. The construction uses a good open in the chain family directly. [Proof guide](proof-guide.md) · [Machine-readable roots and comparison hypotheses](route-roots.json)

| Target and project declaration | Upstream result on comparable data | Scope still requiring the project proof |
| --- | --- | --- |
| 1.1 · `affineLine_h1c_hasWeightsAtMost` | Same $H_c^1$ conclusion on a pure arithmetic model, or given a mixed filtration as well as the pointwise bound | The full pointwise upper-bound hypothesis |
| 1.5 · `affineLineExternalTensorPower_hnc_hasWeightsAtMost` | Given a mixed cutoff $w$ for $F$, pull back the factors and tensor them to obtain cutoff $nw$ for $G=F^{\boxtimes n}$. Alternatively supply that cutoff directly for $G$. The upstream estimate $nw+n$ implies $n(w+1)+3$. | Arbitrary pointwise-bounded $F$ with no given mixed filtration |
| 2.1 · `affineLineExternalTensorPower_hnc_hasWeightsAtMost_of_trace_bound` | Under either extra mixed cutoff, the old proof obtains the consequent for all $n\ge2$ without using the trace premise | The trace criterion for the original inputs uses the project’s Frobenius-equivariant injection into the cohomology of $Rj_*j^*G$ |
| 2.2 · `affineLineExternalTensorPower_alternatingTrace_eq_neg_sum` | The trace formula and character orthogonality supply separate steps | No complete old witness for the signed sum over nonzero frequencies, with the same hypersurface and all powers of Frobenius |
| 2.4 · `exists_denseOpen_affineHyperplane_hasWeakLefschetz` | Finite-coefficient generic base change, affine vanishing and adic product base change supply ingredients | No complete old witness producing one dense open for all its hyperplanes and all degrees $e\ne n$ |
| 2.5 · `exists_smooth_chainSection_hasWeakLefschetz_of_hasWeightsAtMost` | Density helps to choose a point of a given good open | No complete old witness for smoothness and all required vanishings on the same section over one finite extension |
| 2.6 · `chainExponentialSum_bound` | Counting-measure Parseval gives the energy identity for one Fourier transform | No complete old witness for the iterated estimate at arbitrary length with independently chosen coordinate weights |

For 1.5 and 2.1 the factor-level old proof uses `AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.upperStar`, `AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.tensorObj` and `AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology`. Supplying the tensor product’s mixed cutoff removes the first two steps. The upstream theorem gives a weight bound, while Lemma 2.2 identifies an alternating trace and Construction 2.5 produces geometric data. Reaching a common cohomological estimate establishes only the shared conclusion indicated in the table. [Pullback](https://github.com/formal-arithmetic-geometry/weil-conjectures/blob/497f33d964609973fe4ed9647a1e5d32369f0d09/WeilConjectures/DeligneLaumon/Reduction/FormalSteps.lean#L115) · [Tensor products](https://github.com/formal-arithmetic-geometry/weil-conjectures/blob/497f33d964609973fe4ed9647a1e5d32369f0d09/WeilConjectures/DeligneLaumon/Reduction/MixedTensor.lean#L98)

## Counts by mathematical scope

Each row below compares two Lean derivations with the same restricted hypotheses and conclusion. Old-only and new-only columns count disjoint mapped lines. “New project” and “new upstream” give the two source origins on the new-only side. The old denominator is old-only plus shared. Positive net values mean fewer mapped lines on the new side. The alternatives overlap extensively and cannot be added. [Scope definitions and executable witnesses](route-roots.json)

| Common input | Old-only | New project | New upstream | Shared | Old total (denominator) | New total | Net lines | Net / old |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1.1, pure, degree-one entry | 51,700 | 17,969 | 7,507 | 1,437,842 | 1,489,542 | 1,463,318 | +26,224 | +1.76% |
| 1.1, pure, all-degree entry | 51,865 | 17,969 | 7,507 | 1,437,842 | 1,489,707 | 1,463,318 | +26,389 | +1.77% |
| 1.1, mixed with pointwise bound | 60,578 | 17,969 | 7,330 | 1,438,032 | 1,498,610 | 1,463,331 | +35,279 | +2.35% |
| 1.5, mixed factor | 61,658 | 9,704 | 5,456 | 1,437,363 | 1,499,021 | 1,452,523 | +46,498 | +3.10% |
| 2.1, mixed factor | 157,037 | 3,101 | 2,275 | 1,342,001 | 1,499,038 | 1,347,377 | +151,661 | +10.12% |
| 1.5, mixed product | 61,296 | 9,704 | 5,489 | 1,437,330 | 1,498,626 | 1,452,523 | +46,103 | +3.08% |
| 2.1, mixed product | 156,656 | 3,101 | 2,289 | 1,341,987 | 1,498,643 | 1,347,377 | +151,266 | +10.09% |

The first two rows use the same pure sheaf. They differ in the upstream entry point, which takes either degree one on a dense open or arbitrary natural degree on the affine line. The mixed 1.1 comparison supplies both the pointwise bound and mixedness. For 1.5 and 2.1 “factor” supplies the mixed cutoff for $F$, and “product” supplies it for $G$.

The temporary witness text sits outside the two libraries. Its imported dependencies are already in the main counts. The following sensitivity calculation also charges each side all physical lines of its witness theorem declarations, including their signatures and any local helper theorems. After the slash are proof-body lines, already included in the wrapper total. All old-only lines in these seven paired scopes belong to upstream.

| Common input | Old wrapper / body | New wrapper / body | Net with wrappers | Old with wrappers (denominator) | Net / old |
| --- | ---: | ---: | ---: | ---: | ---: |
| 1.1, pure, degree-one entry | 12 / 4 | 9 / 1 | +26,227 | 1,489,554 | +1.76% |
| 1.1, pure, all-degree entry | 10 / 2 | 9 / 1 | +26,390 | 1,489,717 | +1.77% |
| 1.1, mixed with pointwise bound | 10 / 2 | 9 / 1 | +35,280 | 1,498,620 | +2.35% |
| 1.5, mixed factor | 62 / 26 | 12 / 1 | +46,548 | 1,499,083 | +3.11% |
| 2.1, mixed factor | 71 / 28 | 19 / 1 | +151,713 | 1,499,109 | +10.12% |
| 1.5, mixed product | 16 / 4 | 13 / 1 | +46,106 | 1,498,642 | +3.08% |
| 2.1, mixed product | 25 / 6 | 20 / 1 | +151,271 | 1,498,668 | +10.09% |

### Footprint of the full statements

| Exact target | Reached, all packages | Mapped project lines | Mapped upstream lines | Names in two packages | Names lacking spans | Project modules | Upstream modules |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1.1 | 295,247 | 17,969 | 1,445,330 | 153,684 | 85,325 | 269 | 11,863 |
| 1.5 | 292,940 | 9,729 | 1,442,767 | 151,392 | 83,607 | 152 | 11,824 |
| 2.1 | 274,076 | 3,143 | 1,344,207 | 135,158 | 74,029 | 57 | 10,999 |
| 2.2 | 283,471 | 1,830 | 1,384,561 | 143,657 | 78,821 | 37 | 11,366 |
| 2.4 | 264,567 | 5,105 | 1,272,762 | 126,596 | 69,289 | 78 | 10,383 |
| 2.5 | 264,638 | 5,903 | 1,272,707 | 126,728 | 69,364 | 87 | 10,389 |
| 2.6 | 35,296 | 112 | 131 | 26 | 8 | 2 | 2 |
| Seven, union | 295,352 | 18,708 | 1,445,641 | 153,771 | 85,374 | 280 | 11,870 |

The seven-root union touches 25,723 whole-file project lines and 2,228,623 whole-file upstream lines. Its two mapped-line columns total 1,464,349. A separate diagnostic compares that union to four upstream declarations used in the restricted proofs of 1.1, 1.5 and 2.1. It finds 60,843 old-only lines, 18,708 new-only project lines, 7,488 new-only upstream lines and 1,438,153 shared lines. Those four declarations do not establish all seven results. The full seven-target net change and its denominator are therefore undetermined.

The private historical archive contains 28 retired purity modules with 6,197 whole-file lines. None owns a declaration in these closures. Their engineering cost remains in the resource account. The inventory records historical file sizes separately.

Upstream still uses its degree-one estimate in the degree-one branch for **arbitrary dense opens**. Its all-degree affine-line result is used after finite direct image and extension by zero, which can introduce singularities. The general mixed bound is also used on smooth proper varieties for a sheaf and its twisted dual to prove purity. Replacing these callers requires proofs for their wider inputs and a rebuilt upstream library. **The verified amount removable from upstream as a whole is undetermined.** [Dense-open caller](https://github.com/formal-arithmetic-geometry/weil-conjectures/blob/497f33d964609973fe4ed9647a1e5d32369f0d09/WeilConjectures/DeligneLaumon/AffineLine/AffineCurveUpper.lean#L357) · [Finite direct images](https://github.com/formal-arithmetic-geometry/weil-conjectures/blob/497f33d964609973fe4ed9647a1e5d32369f0d09/WeilConjectures/DeligneLaumon/Reduction/AffineCurve.lean#L156) · [Smooth proper purity](https://github.com/formal-arithmetic-geometry/weil-conjectures/blob/497f33d964609973fe4ed9647a1e5d32369f0d09/WeilConjectures/ZetaFunction/LissePurity.lean#L80)

## Measurement and reproduction

The frozen project source revision is `1d2a35cad016e9840d47db5143d19573be9999af`, the Peking University revision `497f33d964609973fe4ed9647a1e5d32369f0d09`, and the Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`, with Lean 4.35.0. The public tree has its own Git history. It carries package-relative project sources, the dependency manifest and a trace index identifying the source revision. [Package pins](../lake-manifest.json) · [Trace index](../traces/index.json)

For each exact target, follow constants in the elaborated type and proof through definitions, instances and private proofs, including kernel dependencies of inductives, constructors and recursors. For a specialized witness start from all imported constants in its type, body and comparison helpers. The seven-target union starts from the seven named declarations. Lemma 2.6’s module audit starts from 15 declarations, so the inventory extracts the exact lemma separately. Dependencies in every package participate in traversal. Only `WeilII` and `WeilConjectures` own measured source lines here, including `WeilConjectures.Mathlib` in the latter package.

A valid full declaration span in the compiled position index (`.ilean`) is half-open. Count each physical line it touches, including internal blank lines and comments. An end position at column zero excludes that final line. Union all such lines per file on each side before taking differences and intersections. Lines in comments or imports outside all selected spans contribute zero. Multiple generated declarations may share a span. Names without a valid span add no directly attributed lines, although another span can cover their source. The whole-file footprint counts every line in a module owning a reached declaration, including unrelated contents. [Per-module counts and inclusive ranges](module-inventory.tsv)

In the main pure comparison, 68 old and 54 new imported seeds reached 312,299 and 295,251 declarations across all packages. The uncompressed comparison traces in the respective witness import environments have SHA-256 `f225b2e9afd3069b4799fdbaeb0633471a17b894246db02dafb5e2c518174d3a` and `03d4dd6eb6a7c520f3f87dd2aaa1783055f2ed306cfdc12992ed4e923886835c`. Among the two measured packages, 85,234 of 155,914 old names and 85,325 of 153,688 new names lacked exact spans. All 12,451 modules had position indices. One project dependency had refreshed compiled artifacts relative to an earlier build record. The recheck matched all 271 dependencies in the comparison build and confirmed the same recursive source digest, compiled main target and native dependency trace.

An earlier pure-case inventory resolved generated declarations in a batched import environment. Replaying each witness with its actual imports changed the assignment in three upstream modules. Six lines in `Mathlib.CategoryTheory.Preadditive.EndoFunctor` (108–109, 111–112, 114–115) and two in `CategoryTheory.Endofunctor.IsoAlgebra` (101–102) moved from shared to old-only. Eight in `CategoryTheory.Endofunctor.IsoAlgebraCreatesLimits` (40–41, 43–44, 46–47, 49–50) became new-only. All three names have the package prefix `WeilConjectures.`. This accounts for the entire difference from the earlier inventory’s 51,692 old-only, 7,499 new-only upstream and 1,437,850 shared lines. The two derivation totals still give a saving of 26,224 lines. All module source and position-index hashes agree. [Per-module ranges](module-inventory.tsv)

The public inventory contains 37,316 records (17,172,577 bytes). Each row gives one module and a comma-separated list of the scopes in which its counts and ranges are identical. Select exact scope tokens and sum once per row. The three range fields are one-based inclusive intervals. The file path is relative to the named package. Historical rows have scope `retired-purity` and an empty public path. The public TSV SHA-256 is `fe21451cae890a1848ec9ea8658018289d524b2d064b6b1950b1c693875e9f2d`. The original measurement table, including the list of unmapped kernel names, has SHA-256 `2bd02f629ed73c2e4d77ed07e75288fa1cb546c4be25fe649d75958f0fbc7122`. The 12,451-module pure-case projection has SHA-256 `2f6d874c168922a14b78386f14b6691b9e1c854ab6f62a0c83807219904e6632`.

For example, this sums four mutually exclusive columns from the public TSV for both the main comparison and the seven-target union. For the one-sided union, all mapped lines fall in the two new-side columns.

```sh
python3 - <<'PY'
import csv
from collections import Counter

fields = ("old_only_lines", "new_project_only_lines", "new_upstream_only_lines", "shared_lines")
totals = {scope: Counter() for scope in ("pure-degree-one", "seven-native")}
with open("docs/module-inventory.tsv", newline="", encoding="utf-8") as stream:
    for row in csv.DictReader(stream, delimiter="\t"):
        for scope in totals.keys() & set(row["scopes"].split(",")):
            totals[scope].update({key: int(row[key]) for key in fields})
for scope, counts in totals.items():
    print(scope, *(counts[key] for key in fields))
PY
```

From the public project root, with Python 3, Git and the pinned Lean toolchain available, run the following. The default recount reads frozen ranges, verifies source hashes in both packages and recomputes the totals. The second recount traverses compiled proof bodies and reads their source positions afresh. The appendix documents requirements for private proof data in the compiled packages and the meaning of each scope. [Recount instructions](recount.md)

```sh
lake build
lake build @weil-conjectures/+WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper \
           @weil-conjectures/+WeilConjectures.DeligneLaumon.Reduction.AffineCurve \
           @weil-conjectures/+WeilConjectures.DeligneLaumon.Reduction.FormalSteps \
           @weil-conjectures/+WeilConjectures.DeligneLaumon.Reduction.MixedTensor \
           @weil-conjectures/+WeilConjectures.DeligneLaumon.Reduction.MixedStalk \
           @weil-conjectures/+WeilConjectures.ZetaFunction.LissePurity \
           @weil-conjectures/+WeilConjectures.ZetaFunction.Weights
upstream=.lake/packages/weil-conjectures
test "$(git -C "$upstream" rev-parse HEAD)" = 497f33d964609973fe4ed9647a1e5d32369f0d09
recount_dir=$(mktemp -d) &&
  python3 docs/recount.py --root . --upstream "$upstream" --output "$recount_dir/weilii-ranges.json" &&
  lake env python3 docs/recount.py --root . --upstream "$upstream" --closures --output "$recount_dir/weilii-closures.json" &&
  cmp "$recount_dir/weilii-ranges.json" "$recount_dir/weilii-closures.json"
```

The archived experiment’s source files, the historical compiler receipts and the underlying machine accounts remain in the private project archive. Their historical totals are reported separately. The public recount uses the release tree and pinned packages for the mathematical scopes. [Resource methods and coverage](project-report.md)

The public root commit is the output of `git rev-list --max-parents=0 HEAD` in the release checkout. Both recounts passed for the public candidate with the same mathematical source, Lake configuration and final module traces. Their output agreed byte for byte for 26 scopes. [Recount results](recount.md) · [Frozen inputs](../traces/index.json)
