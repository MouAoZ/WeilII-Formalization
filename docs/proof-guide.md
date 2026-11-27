# Proof guide

The main theorem needs an estimate for one eigenvalue on the affine line. Zhang obtains it from a less sharp estimate in every dimension $n\ge2$. The fixed loss in that estimate disappears on taking $n$th roots. For each $n$, choosing one hypersurface fixes the open complement whose power traces enter the Fourier estimate. [Statements and notation](mathematics.md) · [Zhang, pp. 2–5](https://arxiv.org/pdf/2611.30749v1#page=2)

## From tensor powers to Theorem 1.1

Write $V=H_c^1(\mathbf A^1_{\bar k},E)$ and $G_n=E^{\boxtimes n}$. In total degree $n$, the multidegree $(1,\ldots,1)$ summand of compactly supported Künneth gives a Frobenius-equivariant injection

$$
V^{\otimes n}\ \hookrightarrow\ H_c^n(\mathbf A^n_{\bar k},G_n).
$$

The Lean construction adjoins one coordinate at a time. In the binary Künneth decomposition the inclusion of the $(r,1)$ summand has a left inverse given by projection. Naturality of the exterior product gives Frobenius equivariance. A nonzero $\alpha$-eigenvector of $V$ has a nonzero pure tensor of eigenvalue $\alpha^n$, so Proposition 1.5 gives $|\iota(\alpha)|^n\le q^{(n(w+1)+3)/2}$. The positive $n$th root is $q^{(w+1)/2+3/(2n)}$. Letting $n\to\infty$ gives Theorem 1.1. [Künneth injection](../WeilII/Paper/AffineLineCompactSupportKunnethInjection.lean) · [Eigenvalue of a tensor power](../WeilII/LinearAlgebra/PositiveTensorPowerEigenvalue.lean) · [Theorem 1.1](../WeilII/Targets/AffineLineWeightBound.lean)

## Where the hypersurface comes from

Zhang derives Construction 2.5 by applying Theorem 2.4 to the graph of $Q_n=\sum_{i=1}^{n-1}x_i x_{i+1}$. Both geometric proofs in Lean use Katz’s comparison for a general hyperplane. The construction applies that comparison directly to the graph. Proposition 1.5 and the weighted Construction 2.5 both call the helper `WeilII.exists_smooth_chainSection_hasWeakLefschetz` for an arbitrary lisse $E$ on the line. [Zhang, p. 3](https://arxiv.org/pdf/2611.30749v1#page=3) · [Construction helper](../WeilII/Targets/Construction25.lean) · [Proposition 1.5](../WeilII/Targets/ExternalTensorPowerWeightBound.lean)

| | Theorem 2.4 | Construction 2.5 as used for Proposition 1.5 |
| --- | --- | --- |
| Morphism | Any quasi-finite $\mathbf A^n_{\bar k}\to\mathbf A^N_{\bar k}$, $N>0$ | The closed graph $x\mapsto(x,Q_n(x))$, $n\ge2$ |
| Sheaf | Any lisse $G$ on the geometric source | The geometric external power of the given arithmetic $E$ |
| Parameters | A dense nonempty open, every geometric hyperplane in it | One tuple $(a,c)$ over a finite extension, last graph coefficient normalized to one |
| Conclusion | All off-middle groups vanish on each such section | The same section is smooth over the finite field of definition and has all off-middle groups zero geometrically |

**The common comparison.** Embed the affine target in projective space, let $f$ be the composite, $B$ the complement of a hyperplane, $j:f^{-1}B\hookrightarrow X$ the inclusion, and $h:f^{-1}B\to B$ the restriction. Given a constructible sheaf $L$, Katz A.3–A.4 yields one dense open of hyperplanes on which the map

$$
 H_c^r(B,Rh_*j^*L)\ \longrightarrow\ H^r(X,j_!j^*L)
$$

is an isomorphism in every degree. Apply it to the twisted dual $L=G^\vee(n)$. Open-complement Verdier duality identifies the dual of $H_c^e(X,Rj_*j^*G)$ with the ordinary group on the right in degree $r=2n-e$. [Katz, Appendix A, pp. 219–221](https://web.math.princeton.edu/~nmk/old/ACT.pdf#page=72) · [Generic hyperplane comparison](../WeilII/Paper/KatzGenericHyperplaneCohomologyComparison.lean) · [Open-complement duality](../WeilII/AlgebraicGeometry/OpenComplementVerdierDuality.lean)

**General Theorem 2.4.** When $e<n$, one has $r>n$, and Artin’s cohomological dimension bound on affine $X$ kills $H^r(X,j_!j^*L)$. When $e>n$, one has $r<n$. On the comparison open, duality on the smooth source of $h$ reduces vanishing of $H_c^r(B,Rh_*j^*L)$ to ordinary cohomology in degree $2n-r>n$. Here quasi-finiteness gives a constructible sheaf on the affine closure of the image in $B$, of dimension at most $n$. The same affine bound applies there. Restricting the open to the affine-hyperplane parameters gives the stated quantifier over all its geometric points. [Quasi-finite compact-support vanishing](../WeilII/AlgebraicGeometry/QuasiFiniteAffineCompactVanishing.lean) · [Lisse form of Katz A.5](../WeilII/Paper/KatzGenericHyperplaneLisseExtensionByZero.lean) · [Theorem 2.4](../WeilII/Targets/Theorem24.lean)

**The chain graph.** In the normalized parameter chart the pulled-back hyperplane equation is $P(x)=Q_n(x)+a\cdot x+c$. The comparison open contains a principal open $D(g)$ of this chart with $g\ne0$. For this graph there is an explicit affine compactification of the restricted image in $B$. Put $t=1/P(x)$ and $v=x/P(x)$. The image is the open $t\ne0$ of

$$
Z=\{(t,v):t(1-a\cdot v-ct)-Q_n(v)=0\},
$$

with inverse $x=v/t$. The linear term $t$ makes this a hypersurface in $(n+1)$-space, of dimension at most $n$. For $e>n$, duality and the factorization through $Z$ reduce the comparison group to ordinary degree-$e$ cohomology of a constructible extension by zero on this affine $Z$, which vanishes. For $e<n$ the affine bound on $X$ applies as above. This proves weak Lefschetz throughout $D(g)$ for the chosen sheaf. [Graph compactification](../WeilII/Paper/ChainGraphIncidenceCompactification.lean) · [Chain-graph weak Lefschetz](../WeilII/Paper/ChainGraphBasicOpenWeakLefschetz.lean)

**One smooth section over a finite field.** A singular zero of $P$ would satisfy $a=-\nabla Q_n(x)$ and $c=Q_n(x)$ by homogeneity, also in characteristic two. These $n+1$ polynomials in $n$ variables satisfy a nonzero relation $b$, yielding a principal open $D(b)$ of smooth sections. The proof chooses a geometric tuple with $g(a,c)b(a,c)c\ne0$, possible over the infinite field $\bar k$. Adjoining the finitely many entries to $k$ gives a finite extension $L$. Smoothness descends to $L$ and extension of the same polynomial to $\bar k$ recovers the section in $D(g)$. This is the witness used for every subsequent power of Frobenius at this $n$. [Jacobian argument](../WeilII/Paper/ChainSectionGenericSmoothness.lean) · [Choice of the finite-field tuple](../WeilII/Paper/SmoothChainSectionFinitePointInBasicOpen.lean) · [Construction 2.5](../WeilII/Targets/Construction25WithWeights.lean)

## How the power-trace estimate gives Proposition 1.5

Fix $n$ and the field $L$ and section just chosen. Pull $E$ back to $L$. Its pointwise weight bound persists because extending a residue field raises the local Frobenius and the field size to the same power. The external tensor power commutes with this change of constants. Let $j$ denote the complement of the chosen section and put $D=Rj_*j^*G_n$ over $L$. Geometric weak Lefschetz makes $H_c^e(D)$ zero for $e\ne n$. For each $m\ge1$, write $M/L$ for the degree-$m$ extension, $N=|M|$, $F_L$ for geometric Frobenius over $L$ and $T(x)=\prod_i t_m(x_i)$ for the product of the embedded stalk traces over $M$. [Geometric concentration](../WeilII/Paper/GeometricChainSectionConcentration.lean) · [Proof over the field of definition](../WeilII/Paper/WeightBoundOfRationalChainSection.lean)

1. **Convert the trace to a sum (Lemma 2.2).** The Gysin sequence for the smooth divisor and the Grothendieck trace formula express the alternating trace as $\sum_{x\in M^n}T(x)-N\sum_{P(x)=0}T(x)$. The closed term has a shift by two and Tate twist $(-1)$, so its sign from the shift is positive and $F_L^m$ contributes the factor $N$. For a nontrivial additive character $\psi$ of $L$, put $\psi_m=\psi\circ\operatorname{Tr}_{M/L}$. Orthogonality gives $\sum_{h\in M}\psi_m(hP(x))=N\,\mathbf1_{P(x)=0}$. The $h=0$ term cancels the affine sum. After concentration the middle trace is $(-1)^{n+1}$ times the remaining sum over $h\ne0$. [Gysin and point traces](../WeilII/Paper/ExternalTensorPowerHypersurfaceTrace.lean) · [Lemma 2.2](../WeilII/Targets/Lemma22.lean)
2. **Bound one frequency (Lemma 2.6).** For $h\ne0$, $z\mapsto\psi_m(hz)$ is nontrivial. Absorb each linear term into $t_i(u)=t_m(u)\psi_m(ha_i u)$ and take the unit-modulus factor $\psi_m(hc)$ outside the sum. For the remaining quadratic chain, start with $A_0(y)=1$. Appending a coordinate multiplies $A_j$ by $t_{j+1}$ and takes the unnormalized finite Fourier transform with this character. Multiplication costs at most $\|t_{j+1}\|_\infty$ in counting $L^2$, and Plancherel multiplies the squared norm by $N$. Since $\|A_0\|_2^2=N$, evaluating $A_n$ at $y=0$ bounds the sum by $N^{(n+1)/2}\prod_i\|t_i\|_\infty$. The auxiliary terminal edge vanishes at $y=0$. [Lemma 2.6](../WeilII/Targets/Lemma26.lean) · [Sum over frequencies](../WeilII/Paper/ChainSectionFrequencyBound.lean)
3. **Account for the exponent.** Choose $R$ bounding the stalk ranks. Each embedded trace has modulus at most $R N^{w/2}$ by the pointwise hypothesis and the triangle inequality. There are $N-1$ nonzero frequencies. The middle power trace is therefore bounded by

   $$
   (N-1)N^{(n+1)/2}(R N^{w/2})^n
    \ \le\ R^n N^{(n(w+1)+3)/2}.
   $$

   One can take $C=\max(1,R^n)$ for every $m$, including when $E$ has rank zero. [Uniform bound over the field of definition](../WeilII/Paper/WeightBoundOfRationalChainSection.lean)
4. **Recover eigenvalues (Lemma 2.1).** Set $s=n(w+1)+3$ and $B=|L|^{s/2}$. The power traces of $F_L$ on $H_c^n(D)$ are bounded by $CB^m$. If $\lambda$ runs over its embedded eigenvalues with multiplicity, the generating series of these traces has the rational expression $\sum_\lambda\lambda/(1-\lambda T)$. It converges on $|T|<1/B$. Each distinct nonzero $\lambda$ contributes a pole at $1/\lambda$ with nonzero multiplicity, so $|\lambda|\le B$. The Gysin sequence gives a Frobenius-equivariant injection $H_c^n(G_n)\hookrightarrow H_c^n(D)$. Its preceding term $H_c^{n-2}(Y,i^*G_n(-1))$ vanishes by duality and the affine cohomological dimension bound on the smooth $(n-1)$-fold $Y$. The eigenvalue bound thus holds on $H_c^n(G_n)$ over $L$. [Trace criterion for Frobenius modules](https://github.com/formal-arithmetic-geometry/weil-conjectures/blob/497f33d964609973fe4ed9647a1e5d32369f0d09/WeilConjectures/ZetaLinearAlgebra/FrobeniusModule/TraceBound.lean) · [Gysin injection](../WeilII/AlgebraicGeometry/SmoothHypersurfaceGysinInjection.lean) · [Lemma 2.1](../WeilII/Targets/Lemma21.lean)
5. **Descend the bound.** With $d=[L:k]$, geometric cohomology identifies $F_L$ with $F_k^d$. For each eigenvalue $\alpha$ of $F_k$ this gives $|\iota(\alpha)|^d\le(q^d)^{s/2}$. Taking $d$th roots proves Proposition 1.5 over $k$. These roots remove the degree of the finite field extension. The $n$th roots in Theorem 1.1 then remove the fixed loss in $s$. [Descent along a finite extension](../WeilII/AlgebraicGeometry/AffineSpaceCohomologyWeightDescent.lean) · [Proposition 1.5](../WeilII/Targets/ExternalTensorPowerWeightBound.lean)

## Reading a proof trace

Three questions arise when checking the argument. The mathematical statements identify what the seven Lean types say. Independent comparison checks the declarations against a separate specification with `propext`, `Classical.choice` and `Quot.sound` as the allowed axioms. To check independence from earlier Weil II weight bounds, the recorded traces follow the constants in each elaborated type and proof body through definitions, instances, private helpers and upstream theorems. They also include dependencies of inductive declarations and recursor rules. [Mathematical statements](mathematics.md) · [Release trace index](../traces/index.json)

For example, `AlgebraicGeometry.hasWeightsAtMostOver_compactlySupportedCohomology_affineLine` and `AlgebraicGeometry.WeilComplex.IsMixedOfWeightsAtMost.derivedLowerShriek` are excluded. A helper that used either result would bring it into the transitive closure. The pointwise bound on $E$ is an input hypothesis. The power-trace criterion is a finite-dimensional linear algebra result, and Lemma 2.6 uses Plancherel on functions on a finite field. These are the sources of the bounds above. The exclusion test compares exact declaration names against the published catalogue. [Excluded declarations](../traces/excluded-declarations.txt)

In `traces/index.json`, look up a paper identifier such as `construction-2-5` in `targets`, then use its `module` to find a record in `modules`. The module record lists all its `roots`, the `reachable` declaration count, the source hash `sourceSha256`, audit `inputKey`, and `traceSha256`. The object is `traces/objects/<traceSha256>.jsonl.gz`. Hash the **decompressed UTF-8 bytes**, including newlines. Each JSON line is an array `[declaration, firstDiscoveryParent, declaringModule]`. Follow parents back to a self-parented root and reverse the list to read one chain of dependencies. The closure covers all declarations emitted by the module together, including private ones. A row records a single witness path even when several roots or paths reach the same declaration. [Index and column names](../traces/index.json)

Run the following from the repository root with Python 3. It checks the source and trace fingerprints for Construction 2.5, checks the declaration count and excluded names, and prints a path to the graph-specific weak Lefschetz result. The final two lines test membership of the general Theorem 2.4 declaration and the shared Katz comparison in this same closure.

```sh
python3 - <<'PY'
import gzip
import hashlib
import json
from pathlib import Path

traces = Path("traces")
index = json.loads((traces / "index.json").read_text())
target = index["targets"]["construction-2-5"]
module = index["modules"][target["module"]]
source = Path(*target["module"].split(".")).with_suffix(".lean")
assert hashlib.sha256(source.read_bytes()).hexdigest() == module["sourceSha256"]
digest = module["traceSha256"]
path = traces / "objects" / (digest + ".jsonl.gz")
parents = {}
sha = hashlib.sha256()
with gzip.open(path, "rb") as stream:
    for line in stream:
        sha.update(line)
        name, parent, owner = json.loads(line)
        parents[name] = parent
assert sha.hexdigest() == digest
assert len(parents) == module["reachable"]

excluded = set((traces / "excluded-declarations.txt").read_text().splitlines())
assert not excluded.intersection(parents)
tip = "WeilII.exists_chainSection_basicOpen_hasWeakLefschetz"
chain = [tip]
while parents[chain[-1]] != chain[-1]:
    chain.append(parents[chain[-1]])
assert chain[-1] in module["roots"]
print(" -> ".join(reversed(chain)))
print("Theorem 2.4:", index["targets"]["theorem-2-4"]["declaration"] in parents)
print("Katz comparison:", "WeilII.exists_denseOpen_isIso_hyperplaneCohomologyComparison" in parents)
PY
```

For the chain-graph proof the two membership results are `False` and `True` respectively. To inspect Theorem 2.4’s own quasi-finite argument, select its separate module record. To examine exclusion coverage across the library, repeat the digest, count and name checks for each record in `modules`. [General hyperplane proof](../WeilII/Targets/Theorem24.lean) · [Trace index](../traces/index.json)

The index also identifies the checker under `targets[paperIdentifier].proofKernel`. For 1.5, 2.1, 2.2, 2.4, 2.5 and 2.6 the default Lean kernel accepted the solution after official statement and permitted-axiom comparison. For 1.1, the official comparator checked the statement and permitted axioms, and 16-thread NanoDa accepted that exact solution export. Its SHA-256 is `dbdbe1c50f3e12ff9b7a41cd351f7b56ef39c83addce84eae478dd71be35c597`. The 297,335 declarations checked by NanoDa belong to the exported environment. The 295,247 entries in the main theorem’s trace count declarations reachable from the target’s elaborated type and proof. [Acceptance index](../traces/index.json) · [Resource accounting](project-report.md)
