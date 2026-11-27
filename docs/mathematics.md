# The seven mathematical statements

## Theorem 1.1 · Weights on the affine line

Fix a finite field $k=\mathbf F_q$, a prime $\ell\nmid q$, an embedding $\iota:\overline{\mathbf Q}_\ell\hookrightarrow\mathbf C$, a real number $w$, and a finite-rank lisse $\overline{\mathbf Q}_\ell$-sheaf $E$ on $\mathbf A^1_k$. Assume that for every $m\ge1$, every $x\in\mathbf A^1(\mathbf F_{q^m})$, and every eigenvalue $\gamma$ of geometric Frobenius at $x$ relative to $\mathbf F_{q^m}$, one has $|\iota(\gamma)|\le q^{mw/2}$. Then every eigenvalue $\alpha$ of geometric Frobenius on $H_c^1(\mathbf A^1_{\bar k},E)$ satisfies

$$
|\iota(\alpha)|\le q^{(w+1)/2}.
$$

The hypothesis permits an inequality at each stalk and any real upper bound $w$. Lean’s declaration is `WeilII.affineLine_h1c_hasWeightsAtMost`. [Theorem 1.1, p. 1](https://arxiv.org/pdf/2611.30749v1#page=1) · [WeilII.Targets.AffineLineWeightBound](../WeilII/Targets/AffineLineWeightBound.lean)

### Frobenius, stalks and cohomology

- **Sheaf and field.** `ProEtale.AdicSheaf ℓ (affineLine k)` with `IsAdicLisseSheaf` describes a module sheaf locally finite free on the pro-étale site of the line over $k$. The characteristic condition in Lean is `ringChar k ≠ ℓ` for prime $\ell$, and `PadicAlgCl ℓ` is the algebraic closure of $\mathbf Q_\ell$. A unital ring map from this field to $\mathbf C$ is injective. [Lean statement](../WeilII/Targets/AffineLineWeightBound.lean)
- **Geometric Frobenius.** Write $\pi:X_{\bar k}\to X$ for the geometric fibre projection. The inverse of $b\mapsto b^q$ on $\bar k$ induces $g$ on the geometric fibre. `WeilSheaf.geometricFiberPullback` equips $\pi^*E$ with its canonical isomorphism $g^*\pi^*E\simeq\pi^*E$. This is the Weil structure used both on stalks and on cohomology. We write $F$ for the action of one geometric Frobenius over the indicated ground field. [Upstream construction](https://github.com/formal-arithmetic-geometry/weil-conjectures/blob/497f33d964609973fe4ed9647a1e5d32369f0d09/WeilConjectures/WeilSheaf/GeometricFiberPullback.lean)
- **Pointwise weights.** `WeilSheaf.HasWeightsAtMost` tests closed points $z$ of the line. If $d=[\kappa(z):k]$, the test for $F_z$ is $|\iota(\gamma)|\le(q^d)^{w/2}$. A point above $z$ over $\mathbf F_{q^m}$ has $d\mid m$ and local Frobenius with eigenvalues $\gamma^{m/d}$. Raising the bound to that power gives $q^{mw/2}$. Conversely, taking a point over $\kappa(z)$ tests $m=d$. [Stalk weights](https://github.com/formal-arithmetic-geometry/weil-conjectures/blob/497f33d964609973fe4ed9647a1e5d32369f0d09/WeilConjectures/WeilSheaf/Stalk.lean) · [Comparison under field extension](https://github.com/formal-arithmetic-geometry/weil-conjectures/blob/497f33d964609973fe4ed9647a1e5d32369f0d09/WeilConjectures/WeilSheaf/StalkCharpoly.lean)
- **Weights of cohomology.** Throughout, $H_c^e$ is compactly supported cohomology on the geometric fibre, in integer degree $e$. For the structure map $a$, it is computed from $R\bar a_!$ with the induced Weil action. For such a Frobenius module $V$, `FrobeniusModule.HasWeightsAtMostOver k ι V s` bounds each eigenvalue $\lambda$ of $F$ by $|\iota(\lambda)|\le q^{s/2}$, where `Nat.card k` gives $q$. [Cohomology](https://github.com/formal-arithmetic-geometry/weil-conjectures/blob/497f33d964609973fe4ed9647a1e5d32369f0d09/WeilConjectures/WeilSheaf/Cohomology.lean) · [Frobenius modules](https://github.com/formal-arithmetic-geometry/weil-conjectures/blob/497f33d964609973fe4ed9647a1e5d32369f0d09/WeilConjectures/ZetaLinearAlgebra/FrobeniusModule.lean)

## Proposition 1.5 · External tensor powers

With the data and pointwise hypothesis of Theorem 1.1, take any integer $n\ge2$. Put $X_n=\mathbf A^n_k$, $G_n=E^{\boxtimes n}=\bigotimes_{i=1}^n\mathrm{pr}_i^*E$ and $s_n=n(w+1)+3$. Every eigenvalue $\lambda$ of $F$ on $H_c^n(X_{n,\bar k},G_n)$ satisfies $|\iota(\lambda)|\le q^{s_n/2}$. In `affineLineExternalTensorPower`, each coordinate projection pulls the given Weil sheaf back to $X_n$, and the tensor product carries the induced Weil action. Thus $n$ specifies the number of factors, dimension and cohomological degree. [External tensor power](../WeilII/Paper/AffineLineExternalTensorPower.lean)

Lean’s declaration is `WeilII.affineLineExternalTensorPower_hnc_hasWeightsAtMost`. [Proposition 1.5, pp. 1 and 4](https://arxiv.org/pdf/2611.30749v1#page=1) · [WeilII.Targets.ExternalTensorPowerWeightBound](../WeilII/Targets/ExternalTensorPowerWeightBound.lean)

## Lemma 2.1 · A uniform power-trace criterion

Retain the hypotheses of Proposition 1.5 and fix $n$. Suppose there are a smooth hypersurface $i:Y\hookrightarrow X_n$ over $k$ and a real $C>0$. Let $j$ be its open complement and put $D=Rj_*j^*G_n$ on the ambient space. Assume that **the same $Y$ and $C$** satisfy, for every $m\ge1$,

$$
\left|\iota\!\left(\operatorname{Tr}(F^m\mid H_c^n(X_{n,\bar k},D))\right)\right|
 \le C(q^m)^{s_n/2}.
$$

Then $H_c^n(X_{n,\bar k},G_n)$ has weights at most $s_n$. In `IsSmoothAffineHypersurface` the immersion is regular of codimension one and $Y$ is smooth over the ground field. The criterion depends only on the immersion. `openImmersionDerivedDirectImageOfRestriction` puts the restricted sheaf in degree zero and takes its right derived direct image. [Hypersurface predicate](../WeilII/Paper/SmoothAffineHypersurface.lean) · [Open restriction and derived direct image](../WeilII/AlgebraicGeometry/OpenImmersionDerivedDirectImage.lean)

Lean’s declaration is `WeilII.affineLineExternalTensorPower_hnc_hasWeightsAtMost_of_trace_bound`. [Lemma 2.1, p. 2](https://arxiv.org/pdf/2611.30749v1#page=2) · [WeilII.Targets.Lemma21](../WeilII/Targets/Lemma21.lean)

## Lemma 2.2 · The exponential-sum identity

Use the data of Proposition 1.5. Choose a polynomial $P\in k[X_1,\ldots,X_n]$ whose zero **subscheme** $Y$ is a smooth hypersurface, and any nontrivial additive character $\psi:k\to\mathbf C^\times$. Write $j,D$ as in Lemma 2.1. For each $m\ge1$ put $k_m=\mathbf F_{q^m}$, $\psi_m=\psi\circ\operatorname{Tr}_{k_m/k}$, and let $t_m(b)$ be $\iota$ applied to the trace of the local geometric Frobenius of the $k_m$-point $b$ on $E$. Then

$$
\sum_{e\in\mathbf Z}(-1)^e\,\iota\!\left(\operatorname{Tr}(F^m\mid H_c^e(X_{n,\bar k},D))\right)
 =-\sum_{h\in k_m^\times}\;\sum_{x\in k_m^n}
    \left(\prod_{i=1}^n t_m(x_i)\right)\psi_m(hP(x)).
$$

Only finitely many cohomology groups contribute. Lean uses `∑ᶠ` for the left sum, `FiniteField.galoisExtension k m` for $k_m$, `ψ.compTrace` for $\psi_m$, and the unit group of the extension for the nonzero frequencies. Both sums on the right use counting measure. The field trace is surjective even when the characteristic divides $m$. Lean’s declaration is `WeilII.affineLineExternalTensorPower_alternatingTrace_eq_neg_sum`. [Lemma 2.2 and (2.2.1), p. 3](https://arxiv.org/pdf/2611.30749v1#page=3) · [WeilII.Targets.Lemma22](../WeilII/Targets/Lemma22.lean)

## Theorem 2.4 · General hyperplane weak Lefschetz

Work over $K=\bar k$ with the same coefficient prime. Fix $n\ge0$, $N>0$, a quasi-finite $K$-morphism $u:\mathbf A^n_K\to\mathbf A^N_K$, and any geometric lisse $\overline{\mathbf Q}_\ell$-sheaf $G$ on its source. There exists a nonempty dense Zariski open $U$ of the affine-hyperplane parameter space such that **every** $A\in U(K)$ has the following property. If $j$ includes the complement of the scheme-theoretic inverse image $u^{-1}A$, then

$$
H_c^e(\mathbf A^n_K,Rj_*j^*G)=0\qquad(e\in\mathbf Z,\ e\ne n).
$$

This is `HasWeakLefschetz`, Zhang’s Definition 2.3. Degree $n$ is unrestricted. Lean uses `LocallyQuasiFinite` for the morphism between these affine spaces, which is already quasi-compact and of finite type. The parameters are projective coefficients $[c:a_1:\cdots:a_N]$ with some $a_i\ne0$, representing $c+\sum_i a_i z_i=0$ up to scale. Their union of affine charts is nonempty for $N>0$. Intersecting a dense open with any coefficient chart gives the equivalent generic assertion in normalized coordinates. The sheaf here may be given directly over $K$. [Hyperplane family](../WeilII/Paper/AffineHyperplaneFamily.lean) · [Definition 2.3](../WeilII/Paper/WeakLefschetz.lean)

Lean’s declaration is `WeilII.exists_denseOpen_affineHyperplane_hasWeakLefschetz`. [Theorem 2.4, p. 3](https://arxiv.org/pdf/2611.30749v1#page=3) · [WeilII.Targets.Theorem24](../WeilII/Targets/Theorem24.lean)

## Construction 2.5 · One smooth chain section

Return to the arithmetic sheaf and pointwise hypothesis of Proposition 1.5, and fix $n\ge2$. Write $Q_n(x)=\sum_{i=1}^{n-1}x_ix_{i+1}$. There exist a finite intermediate field $k\subseteq L\subseteq\bar k$, coefficients $a_1,\ldots,a_n,c\in L$, and hence a single equation

$$
P(x)=Q_n(x)+\sum_{i=1}^n a_i x_i+c=0 .
$$

Its zero subscheme is a smooth hypersurface over $L$. After mapping the **same coefficients** into $\bar k$, its geometric zero subscheme satisfies Definition 2.3 for the geometric sheaf underlying $G_n$. The field and coefficients can depend on $E$ and $n$. This is the existence assertion in the paper. The formal target carries the original weight hypothesis, and its geometric proof applies to every lisse $E$ on the line. [Chain polynomial](../WeilII/Paper/ChainSectionPolynomial.lean) · [Geometric sheaf used in the predicate](../WeilII/Paper/GeometricExternalTensorPowerLisse.lean)

Lean’s declaration is `WeilII.exists_smooth_chainSection_hasWeakLefschetz_of_hasWeightsAtMost`. [Construction 2.5, pp. 3–4](https://arxiv.org/pdf/2611.30749v1#page=3) · [WeilII.Targets.Construction25WithWeights](../WeilII/Targets/Construction25WithWeights.lean)

## Lemma 2.6 · A finite-field Fourier bound

Let $k$ be any finite field of order $q$, $n\ge2$, $\psi:k\to\mathbf C^\times$ any nontrivial additive character, and $t_1,\ldots,t_n:k\to\mathbf C$ arbitrary functions chosen independently. With the consecutive-pair quadratic $Q_n$ from Construction 2.5,

$$
\left|\sum_{x\in k^n}\left(\prod_{i=1}^n t_i(x_i)\right)\psi(Q_n(x))\right|
 \le q^{(n+1)/2}\prod_{i=1}^n\|t_i\|_\infty,
 \qquad \|t_i\|_\infty=\max_{b\in k}|t_i(b)|.
$$

Lean takes the phase `chainSectionPolynomial 0 0`. A tuple is a function `Fin n → k` and the norm on the complex-valued functions on this finite field is the supremum norm. For example, with $n=3$ and all $t_i=1$, summing $\psi(x_2(x_1+x_3))$ over $x_1,x_3$ leaves just the $x_2=0$ contribution, $q^2$. This equals the bound. Lean’s declaration is `WeilII.chainExponentialSum_bound`. [Lemma 2.6, pp. 4–5](https://arxiv.org/pdf/2611.30749v1#page=4) · [WeilII.Targets.Lemma26](../WeilII/Targets/Lemma26.lean)

## Verification of the seven statements

The independent specification fixes the seven declarations together with the project definitions on which their meanings depend. The official comparator matched each target and checked its permitted axioms, `propext`, `Classical.choice` and `Quot.sound`. For 1.5, 2.1, 2.2, 2.4, 2.5 and 2.6 the default Lean kernel accepted the proof export. For 1.1 a 16-thread NanoDa run checked the same final solution export as the comparator, with zero typechecking errors and one diagnostic printing the axiom list. The index identifies each declaration, its checker and its export digests. [Acceptance and trace index](../traces/index.json) · [Following a proof](proof-guide.md)
