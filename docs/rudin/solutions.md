# Rudin exercises: statements and solutions

This article converts the exercise proofs in this repository from Lean into
mathematical prose. The source is Walter Rudin's *Principles of Mathematical
Analysis*, Third Edition. Statements below summarize the formal results,
not the complete text of the book.

## Scope and reading guide

There is one entry for each of the **281 exercise files** currently present.
The [inventory](../../exercises.json) records **262 verified resolutions**:
254 proved as stated and 8 resolved by counterexamples and explicit
corrections. The remaining **19 entries** describe formalizations whose
inventory verification is pending. Their stated limits distinguish completed
results from partial constructions and unresolved source obligations.
This article does not claim that all 287 exercises in the book are solved.

Each entry gives the mathematical statement, proof, Lean source, relevant
declarations, and current inventory status. “Verified” refers to the repository's
recorded source review and proof checks, not a new formal verification of this
prose. Short Lean declaration names refer to the namespaces in their linked
source files. A pending entry is not a claim of full exercise completion.

Source corrections remain separate from the original claims. See the
[source record](source.md), [source issues](errata.md),
[clarification contracts](source-clarifications.md), and
[progress report](progress.md). Shared support lemmas are included through the
exercise results that use them; they are not additional solved exercises.
The conversion does not change Lean proofs or verification records.

The article uses standard mathematical notation:

- $\mathbb N$, $\mathbb Q$, $\mathbb R$, and $\mathbb C$ denote the natural,
  rational, real, and complex numbers. Lean indices can be shifted to start at zero.
- A convergent numerical series means convergence of ordered partial sums.
  Absolute or unconditional convergence is stated when needed.
- Endpoint derivatives are relative, one-sided derivatives where permitted.
- Riemann–Stieltjes integrals retain their endpoint and jump conventions.
  Measure integrals require the stated integrability or comparison results.
- Almost-everywhere equality does not assert pointwise equality.

## Contents

| Chapter | Article entries | Inventory-verified resolutions |
| --- | ---: | ---: |
| [1. The Real and Complex Number Systems](#chapter-01) | 20 | 20 |
| [2. Basic Topology](#chapter-02) | 30 | 30 |
| [3. Numerical Sequences and Series](#chapter-03) | 25 | 25 |
| [4. Continuity](#chapter-04) | 26 | 26 |
| [5. Differentiation](#chapter-05) | 29 | 29 |
| [6. The Riemann–Stieltjes Integral](#chapter-06) | 19 | 19 |
| [7. Sequences and Series of Functions](#chapter-07) | 26 | 26 |
| [8. Some Special Functions](#chapter-08) | 31 | 31 |
| [9. Functions of Several Variables](#chapter-09) | 31 | 31 |
| [10. Integration of Differential Forms](#chapter-10) | 26 | 7 |
| [11. The Lebesgue Theory](#chapter-11) | 18 | 18 |
| **Total** | **281** | **262** |

No exercise proof file is present for `R10E22`, `R10E24`, `R10E25`, `R10E26`, `R10E27`, `R10E31`.

<a id="chapter-01"></a>

## Chapter 1 — The Real and Complex Number Systems

**Exercises:** [1](#r01e01) · [2](#r01e02) · [3](#r01e03) · [4](#r01e04) · [5](#r01e05) · [6](#r01e06) · [7](#r01e07) · [8](#r01e08) · [9](#r01e09) · [10](#r01e10) · [11](#r01e11) · [12](#r01e12) · [13](#r01e13) · [14](#r01e14) · [15](#r01e15) · [16](#r01e16) · [17](#r01e17) · [18](#r01e18) · [19](#r01e19) · [20](#r01e20)

<a id="r01e01"></a>
### 1.1 — Rational operations preserve irrationality
**Lean source:** [Exercise01.lean](../../Math/Rudin/Chapter01/Exercise01.lean).
**Inventory status:** Verified as stated.

**Statement.** If $r\in\mathbb Q\setminus\{0\}$ and $x\in\mathbb R$ is irrational, both $r+x$ and $rx$ are irrational.

**Proof.** If $r+x$ were rational, subtracting $r$ would make $x$ rational. If $rx$ were rational, division by the nonzero rational $r$ would make $x$ rational. Both conclusions contradict the hypothesis.

**Lean declarations:** `exercise01`.

<a id="r01e02"></a>
### 1.2 — No rational square root of twelve
**Lean source:** [Exercise02.lean](../../Math/Rudin/Chapter01/Exercise02.lean).
**Inventory status:** Verified as stated.

**Statement.** For every $q\in\mathbb Q$, $q^2\ne12$.

**Proof.** A natural number that is a rational square is an integer square. Indeed, if $q=a/b$ is in lowest terms with $b>0$, then $a^2=12b^2$ forces $b=1$, since $a^2$ and $b^2$ are relatively prime. But $3^2<12<4^2$, so $12$ is not an integer square. The Lean proof uses the standard rational-square criterion for natural numbers.

**Lean declarations:** `exercise02`.

<a id="r01e03"></a>
### 1.3 — Multiplicative consequences of the field axioms
**Lean source:** [Exercise03.lean](../../Math/Rudin/Chapter01/Exercise03.lean).
**Inventory status:** Verified as stated.

**Statement.** In any field, let $x\ne0$.

1. If $xy=xz$, then $y=z$.
2. If $xy=x$, then $y=1$.
3. If $xy=1$, then $y=1/x$.
4. $1/(1/x)=x$.

**Proof.** Multiplication of $xy=xz$ by $x^{-1}$ gives $y=z$. Apply this cancellation first to $xy=x\cdot1$, and then to $xy=x(1/x)=1$, to obtain the second and third claims. Finally, $1/x\ne0$ and $(1/x)x=1$, so the third claim applied to $1/x$ gives $x=1/(1/x)$.

**Lean declarations:** `exercise03_a`, `exercise03_b`, `exercise03_c`, `exercise03_d`.

<a id="r01e04"></a>
### 1.4 — Lower bounds precede upper bounds
**Lean source:** [Exercise04.lean](../../Math/Rudin/Chapter01/Exercise04.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $E$ be a nonempty subset of a linearly ordered set. If $\alpha$ is a lower bound of $E$ and $\beta$ is an upper bound, then $\alpha\le\beta$.

**Proof.** Choose $x\in E$. The bound assumptions give $\alpha\le x\le\beta$, and transitivity gives the result.

**Lean declarations:** `exercise04`.

<a id="r01e05"></a>
### 1.5 — Infimum by negation
**Lean source:** [Exercise05.lean](../../Math/Rudin/Chapter01/Exercise05.lean).
**Inventory status:** Verified as stated.

**Statement.** If $A\subseteq\mathbb R$ is nonempty and bounded below, then $-A=\{-a:a\in A\}$ is nonempty and bounded above, and

$$
\inf A=-\sup(-A).
$$

**Proof.** An element $a\in A$ gives $-a\in-A$. A lower bound $b$ of $A$ gives the upper bound $-b$ of $-A$. Write $s=\sup(-A)$. For each $a\in A$, $-a\le s$, hence $-s\le a$. Thus $-s$ is a lower bound of $A$. If $c$ is any lower bound, $-c$ bounds $-A$ above, so $s\le-c$ and $c\le-s$. Therefore $-s$ is the greatest lower bound.

**Lean declarations:** `exercise05`.

<a id="r01e06"></a>
### 1.6 — Powers constructed from roots and suprema
**Lean source:** [Exercise06.lean](../../Math/Rudin/Chapter01/Exercise06.lean).
**Inventory status:** Verified as stated.

**Statement.** Fix $b>1$.

1. For $a>0$ and an integer $n>0$, there is a unique positive $u$ satisfying $u^n=a$. If integers $m,n,p,q$ satisfy $n,q>0$ and $m/n=p/q$, the positive $n$th root of $b^m$ equals the positive $q$th root of $b^p$. Thus these roots define $b^r$ unambiguously for $r\in\mathbb Q$, with every fraction representation giving the same value.
2. For $r,s\in\mathbb Q$, $b^{r+s}=b^rb^s$.
3. For real $x$, put

   $$
   B(x)=\{b^t:t\in\mathbb Q,\ t\le x\}.
   $$

   This set is nonempty and bounded above. For rational $r$, $b^r=\sup B(r)$. Consequently $b^x:=\sup B(x)$ extends the rational definition.
4. For real $x,y$, these supremum-defined powers satisfy $b^{x+y}=b^xb^y$.

**Proof.** To distinguish the construction from the library power function, write $P_b(x)$ for the standard real power. The standard laws for positive bases give

$$
P_a(1/n)>0,\qquad P_a(1/n)^n=a.
$$

If $u>0$ and $u^n=a$, raising both sides to the power $1/n$ gives $u=P_a(1/n)$. Thus the root selected by its defining equation exists, is unique, and equals this standard power. In particular, the positive $n$th root of $b^m$ is $P_b(m/n)$. Equal fractions therefore give equal roots, even when their numerators are negative. The standard addition law now gives the rational addition law.

Choose a rational $t<x$ to see that $B(x)$ is nonempty. Monotonicity gives $b^t=P_b(t)\le P_b(x)$ whenever $t\le x$, so $B(x)$ is bounded above. If $x=r$ is rational, $b^r$ belongs to $B(r)$ and bounds it above; it is therefore its maximum and supremum.

For arbitrary real $x$, let $S=\sup B(x)$. We already have $S\le P_b(x)$. If $z<P_b(x)$, continuity of $P_b$ gives a neighborhood of $x$ on which $P_b(t)>z$. Rational density supplies a rational $t<x$ in that neighborhood. Then $z<b^t\le S$. This proves $S=P_b(x)$. The standard addition law for $P_b$ now proves the addition law for the constructed real powers.

**Scope.** The roots and suprema are the actual definitions in the file. Their agreement with standard real powers is proved, not assumed as a definition. The condition in $B(x)$ is $t\le x$, including its endpoint.

**Lean declarations:** `exercise06_a`, `exercise06_root_exists`, `exercise06_root_spec`, `exercise06_rationalPower_fraction`, `exercise06_b`, `exercise06_c_supremum`, `exercise06_lowerPowers_nonempty`, `exercise06_lowerPowers_bddAbove`, `exercise06_realPower_eq_rpow`, `exercise06_c_real_power`, `exercise06_d`.

<a id="r01e07"></a>
### 1.7 — A logarithm obtained from a supremum
**Lean source:** [Exercise07.lean](../../Math/Rudin/Chapter01/Exercise07.lean).
**Inventory status:** Verified as stated.

**Statement.** Fix $b>1$ and use the powers constructed in Exercise 1.6. For each $y>0$, there is exactly one real $x$ such that $b^x=y$. The construction has these seven steps:

1. $b^n-1\ge n(b-1)$ for each positive integer $n$; the formal result also includes $n=0$.
2. $b-1\ge n(b^{1/n}-1)$ for each positive integer $n$.
3. If $t>1$ and the positive integer $n$ satisfies $n>(b-1)/(t-1)$, then $b^{1/n}<t$.
4. If $b^w<y$, then $b^{w+1/n}<y$ for every sufficiently large positive integer $n$.
5. If $b^w>y$, then $b^{w-1/n}>y$ for every sufficiently large positive integer $n$.
6. $A=\{w\in\mathbb R:b^w<y\}$ is nonempty and bounded above, and $x=\sup A$ satisfies $b^x=y$.
7. Any two solutions coincide.

**Proof.** Bernoulli's inequality, applied to $b=1+(b-1)$, gives (1). Apply (1) with base $b^{1/n}>1$ and use $(b^{1/n})^n=b$ to get (2). Under the hypothesis of (3),

$$
n(b^{1/n}-1)\le b-1<n(t-1),
$$

which gives $b^{1/n}<t$.

For (4), set $t=y/b^w>1$. Choose an integer threshold $N\ge1$ larger than $(b-1)/(t-1)$. For every $n\ge N$, part (3) and the addition law give $b^{w+1/n}=b^wb^{1/n}<y$. For (5), use $t=b^w/y>1$ instead. Then $b^{1/n}<b^w/y$ and hence $b^{w-1/n}=b^w/b^{1/n}>y$ for all sufficiently large $n$.

The powers $b^n$ are unbounded, for example by (1). Choose $n$ with $b^n>1/y$; then $-n\in A$. Choose $m$ with $b^m>y$. Strict monotonicity of powers shows that every $w\in A$ satisfies $w<m$, so $A$ is bounded above.

Let $x=\sup A$. If $b^x<y$, part (4) gives $x+1/N\in A$ for some $N>0$, contrary to $x$ being an upper bound. If $b^x>y$, part (5) gives $b^{x-1/N}>y$. Every $w\in A$ then satisfies $w<x-1/N$, so $x-1/N$ is an upper bound smaller than $x$. Both alternatives are impossible, proving $b^x=y$. Finally, strict monotonicity makes $x\mapsto b^x$ injective, proving uniqueness.

**Lean declarations:** `exercise07_a`, `exercise07_b`, `exercise07_c`, `exercise07_d`, `exercise07_e`, `exercise07_A_nonempty`, `exercise07_A_bddAbove`, `exercise07_f`, `exercise07_g`, `exercise07`.

<a id="r01e08"></a>
### 1.8 — The complex field cannot be ordered
**Lean source:** [Exercise08.lean](../../Math/Rudin/Chapter01/Exercise08.lean).
**Inventory status:** Verified as stated.

**Statement.** No linear order on $\mathbb C$ makes its usual field operations into an ordered field.

**Proof.** In an ordered field every square is nonnegative. Thus $i^2=-1$ would be nonnegative. But the ordered-field axioms give $0<1$, hence $-1<0$, a contradiction. This excludes every proposed linear order, not merely a particular one.

**Lean declarations:** `exercise08`.

<a id="r01e09"></a>
### 1.9 — Lexicographic order lacks least upper bounds
**Lean source:** [Exercise09.lean](../../Math/Rudin/Chapter01/Exercise09.lean).
**Inventory status:** Verified as stated.

**Statement.** Define

$$
a+bi<c+di\quad\Longleftrightarrow\quad a<c\ \text{or}\ (a=c\ \text{and}\ b<d).
$$

This is a strict linear order on $\mathbb C$, but it does not have the least-upper-bound property. The imaginary axis $E=\{z:\operatorname{Re}z=0\}$ is a counterexample: its upper bounds are exactly the numbers with positive real part.

**Proof.** Irreflexivity follows from irreflexivity of the real order. For transitivity, if either comparison increases the real coordinate, the composite comparison does too; otherwise all three real coordinates agree and transitivity holds in the imaginary coordinates. Comparing real coordinates, and then imaginary coordinates when necessary, gives trichotomy.

If $\operatorname{Re}u>0$, every point of $E$ precedes $u$. Conversely, an upper bound $u$ must dominate $i(\operatorname{Im}u+1)$. Since its imaginary coordinate is too small for the equal-real-coordinate alternative, $\operatorname{Re}u>0$. The set $E$ contains $0$ and is bounded above by $1$. For any upper bound $u$, the number $u-i$ is a strictly smaller upper bound with the same positive real part. Thus no least upper bound exists.

**Lean declarations:** `exercise09_lt_iff`, `exercise09_linear_order`, `exercise09_upperBounds`, `exercise09_no_lub`.

<a id="r01e10"></a>
### 1.10 — Explicit complex square roots
**Lean source:** [Exercise10.lean](../../Math/Rudin/Chapter01/Exercise10.lean).
**Inventory status:** Verified as stated.

**Statement.** For $w=u+iv\in\mathbb C$, set

$$
a=\sqrt{\frac{|w|+u}{2}},\qquad b=\sqrt{\frac{|w|-u}{2}},\qquad z=a+bi.
$$

Both coefficients are nonnegative. If $v\ge0$, then $z^2=w$; if $v\le0$, then $\overline z^{\,2}=w$. Let $\rho=z$ when $v\ge0$, and $\rho=\overline z$ otherwise. For $w\ne0$, the square roots are exactly the two distinct numbers $\rho$ and $-\rho$. For $w=0$, the unique square root is $0$.

**Proof.** Since $|u|\le|w|$, the radicands are nonnegative. Their squares give $a^2-b^2=u$. Also,

$$
(2ab)^2=4a^2b^2=|w|^2-u^2=v^2.
$$

Both $2ab$ and $|v|$ are nonnegative, so $2ab=|v|$. Therefore $z^2=u+i|v|$ and $\overline z^{\,2}=u-i|v|$, proving both sign-dependent formulas, including $v=0$.

For any $t$, the equation $t^2=w=\rho^2$ factors as $(t-\rho)(t+\rho)=0$. Thus $t=\rho$ or $t=-\rho$. If $w\ne0$, then $\rho\ne0$, so these roots are distinct. If $w=0$, the equation $t^2=0$ implies $t=0$.

**Lean declarations:** `exercise10_nonnegative_imaginary`, `exercise10_nonpositive_imaginary`, `exercise10_nonzero_roots`, `exercise10_zero_root`.

<a id="r01e11"></a>
### 1.11 — Radius and unit factor
**Lean source:** [Exercise11.lean](../../Math/Rudin/Chapter01/Exercise11.lean).
**Inventory status:** Verified as stated.

**Statement.** Every $z\in\mathbb C$ has a representation $z=rw$ with $r\ge0$ and $|w|=1$. The radius is always uniquely determined as $r=|z|$. The unit factor is unique exactly when $z\ne0$. For $z=0$, all representations have $r=0$ and arbitrary $w$ of modulus one.

**Proof.** For $z\ne0$, take $r=|z|$ and $w=z/|z|$. Then $|w|=1$ and $rw=z$. For $z=0$, take $r=0,w=1$. In any admissible representation, $|z|=|r||w|=r$, which proves radius uniqueness. When $z\ne0$, division by this positive radius forces $w=z/|z|$. When $z=0$, the radius must vanish, and every unit $w$ works. In particular, the distinct choices $1$ and $-1$ show that the unit factor is not unique.

**Lean declarations:** `exercise11`, `exercise11_radius_uniqueness`, `exercise11_unit_uniqueness`, `exercise11_unit_unique_iff`, `exercise11_zero_choices`.

<a id="r01e12"></a>
### 1.12 — The finite triangle inequality
**Lean source:** [Exercise12.lean](../../Math/Rudin/Chapter01/Exercise12.lean).
**Inventory status:** Verified as stated.

**Statement.** For complex numbers $z_1,\ldots,z_n$,

$$
\left|\sum_{j=1}^n z_j\right|\le\sum_{j=1}^n|z_j|.
$$

The formal result permits every $n\ge0$, including the empty sum.

**Proof.** The empty case is $0\le0$. If the result holds for $n$, the triangle inequality gives

$$
\left|\sum_{j=1}^{n+1}z_j\right|\le\left|\sum_{j=1}^nz_j\right|+|z_{n+1}|\le\sum_{j=1}^{n+1}|z_j|.
$$

Induction proves the claim.

**Lean declarations:** `exercise12`.

<a id="r01e13"></a>
### 1.13 — The reverse triangle inequality
**Lean source:** [Exercise13.lean](../../Math/Rudin/Chapter01/Exercise13.lean).
**Inventory status:** Verified as stated.

**Statement.** For $x,y\in\mathbb C$,

$$
\bigl||x|-|y|\bigr|\le|x-y|.
$$

**Proof.** From $x=(x-y)+y$, the triangle inequality gives $|x|-|y|\le|x-y|$. Interchanging $x,y$ gives $|y|-|x|\le|y-x|=|x-y|$. Together these inequalities bound the absolute value of the difference.

**Lean declarations:** `exercise13`.

<a id="r01e14"></a>
### 1.14 — A sum of squared moduli
**Lean source:** [Exercise14.lean](../../Math/Rudin/Chapter01/Exercise14.lean).
**Inventory status:** Verified as stated.

**Statement.** If $z\in\mathbb C$ and $|z|=1$, then $|1+z|^2+|1-z|^2=4$.

**Proof.** The parallelogram identity gives

$$
|1+z|^2+|1-z|^2=2|1|^2+2|z|^2=4.
$$

**Lean declarations:** `exercise14`.

<a id="r01e15"></a>
### 1.15 — Equality in finite complex Schwarz inequality
**Lean source:** [Exercise15.lean](../../Math/Rudin/Chapter01/Exercise15.lean).
**Inventory status:** Verified as stated.

**Statement.** For $a,b\in\mathbb C^n$,

$$
\left|\sum_{j=1}^na_j\overline{b_j}\right|^2\le
\left(\sum_{j=1}^n|a_j|^2\right)\left(\sum_{j=1}^n|b_j|^2\right).
$$

Equality holds exactly when $a=0$, or $b=0$, or $b=ca$ for some nonzero $c\in\mathbb C$. Equivalently, equality holds if and only if $a=0$ or $b=ca$ for some scalar $c$. This includes $n=0$ and both zero-vector cases.

**Proof.** Give $\mathbb C^n$ its Euclidean norm and use the convention

$$
\langle b,a\rangle=\sum_j a_j\overline{b_j},\qquad \|a\|^2=\sum_j|a_j|^2.
$$

Cauchy–Schwarz gives $|\langle b,a\rangle|\le\|a\|\|b\|$; squaring gives the displayed inequality. The standard inner-product equality theorem states that equality holds precisely when $a=0$ or $b=ca$ for some scalar $c$. It applies also to the squared equality because both unsquared sides are nonnegative. If the scalar is zero, then $b=0$; otherwise it gives the stated nonzero-scalar branch. Conversely each of these three branches gives equality, by direct substitution or by the same equality theorem.

**Lean declarations:** `exercise15`, `exercise15_inner_sum`, `exercise15_norm_sq_sum`, `exercise15_schwarz`.

<a id="r01e16"></a>
### 1.16 — Intersections of equal-radius spheres
**Lean source:** [Exercise16.lean](../../Math/Rudin/Chapter01/Exercise16.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $x,y\in\mathbb R^k$ satisfy $d=\|x-y\|>0$, and let $r>0$. The number of points $z$ such that $\|z-x\|=\|z-y\|=r$ is:

| Dimension | $2r>d$ | $2r=d$ | $2r<d$ |
| --- | --- | --- | --- |
| $k\ge3$ | Infinitely many | One | None |
| $k=2$ | Two | One | None |
| $k=1$ | None | One | None |

More generally, for any dimension and $r\ge0$, with $m=(x+y)/2$,

$$
\|z-x\|=\|z-y\|=r
\quad\Longleftrightarrow\quad
\langle y-x,z-m\rangle=0,\qquad
\|z-m\|^2=r^2-\frac{\|y-x\|^2}{4}.
$$

If $s\ge0$ and $s^2=r^2-\|y-x\|^2/4$, the locus is exactly the image of the radius-$s$ sphere in $(\mathbb R(y-x))^\perp$ under $u\mapsto m+u$.

**Proof.** Write $u=z-m$ and $v=(y-x)/2$. Then $z-x=u+v$ and $z-y=u-v$, so expansion gives

$$
\|z-x\|^2=\|u\|^2+\frac{d^2}{4}+\langle y-x,u\rangle,
$$

$$
\|z-y\|^2=\|u\|^2+\frac{d^2}{4}-\langle y-x,u\rangle.
$$

Adding and subtracting proves the equivalence; the reverse implication uses nonnegativity to pass from squared norms to norms. It also proves the asserted sphere-image description.

If $2r<d$, the triangle inequality would give $d\le\|x-z\|+\|z-y\|=2r$, a contradiction. Under $r>0$, the squared radius $r^2-d^2/4$ is negative in this case, so it cannot be the square of a real norm. No square-root construction is valid for this branch. If $2r=d$, the squared radius is zero, forcing $z=m$, which does satisfy both equations.

Suppose $2r>d$. Since $x\ne y$, the perpendicular subspace has dimension $k-1$, and $s=\sqrt{r^2-d^2/4}>0$. For $k=1$, that subspace is $\{0\}$, so it has no vector of norm $s$. For $k=2$, it is a line; its radius-$s$ sphere consists of two opposite vectors. Translation preserves their distinctness. For $k\ge3$, its dimension is at least two. A positive-radius sphere in such a space is connected and contains two distinct opposite points; a connected finite subset of a metric space is a singleton, so this sphere is infinite. Its translation is injective and therefore has infinite image.

**Scope.** The bridge and tangency theorem also allow $r=0$ and coincident centers in every dimension. The no-intersection theorem needs only $2r<\|x-y\|$. The dimension-dependent counts above retain the source assumptions $d>0$ and $r>0$.

**Lean declarations:** `exercise16_a`, `exercise16_bridge`, `exercise16_sphere_image`, `exercise16_b`, `exercise16_c`, `exercise16_dimension_two`, `exercise16_dimension_one_cases`.

<a id="r01e17"></a>
### 1.17 — The parallelogram identity and its geometry
**Lean source:** [Exercise17.lean](../../Math/Rudin/Chapter01/Exercise17.lean).
**Inventory status:** Verified as stated.

**Statement.** For $x,y\in\mathbb R^k$,

$$
\|x+y\|^2+\|x-y\|^2=2\|x\|^2+2\|y\|^2.
$$

If four vertices $a,b,c,d$ in order satisfy $a+c=b+d$, then

$$
\|a-c\|^2+\|b-d\|^2=
\|a-b\|^2+\|b-c\|^2+\|c-d\|^2+\|d-a\|^2.
$$

Thus the sum of the squared diagonal lengths equals the sum of the squared side lengths, including degenerate parallelograms.

**Proof.** Expand each squared norm using the inner product. The cross terms $2\langle x,y\rangle$ and $-2\langle x,y\rangle$ cancel. For the geometric version, set $x=b-a$ and $y=d-a$. The relation on vertices gives $c=a+x+y$. The diagonal vectors are $x+y$ and $x-y$, up to sign, and the side lengths are $\|x\|,\|y\|,\|x\|,\|y\|$. Substitution gives the formula without any nondegeneracy assumption.

**Lean declarations:** `exercise17`, `exercise17_geometry`.

<a id="r01e18"></a>
### 1.18 — A nonzero orthogonal vector
**Lean source:** [Exercise18.lean](../../Math/Rudin/Chapter01/Exercise18.lean).
**Inventory status:** Verified as stated.

**Statement.** For $k\ge2$ and every $x\in\mathbb R^k$, there is a nonzero $y\in\mathbb R^k$ with $x\cdot y=0$. In dimension one, such a $y$ exists exactly when $x=0$.

**Proof.** If $x_1=x_2=0$, take $y=e_1$. Otherwise take

$$
y=x_1e_2-x_2e_1.
$$

At least one of its first two coordinates is nonzero, and $x\cdot y=-x_1x_2+x_2x_1=0$. In dimension one, orthogonality is $xy=0$. If $y\ne0$, this forces $x=0$. Conversely, $x=0$ is orthogonal to the nonzero vector $1$.

**Lean declarations:** `exercise18`, `exercise18_vector_spec`, `exercise18_dimension_one`.

<a id="r01e19"></a>
### 1.19 — A distance locus and its zero-radius exception
**Lean source:** [Exercise19.lean](../../Math/Rudin/Chapter01/Exercise19.lean).
**Inventory status:** Verified refutation and correction.

**Statement.** The printed request asks, for arbitrary $a,b\in\mathbb R^k$, for a center $c$ and radius $r>0$ such that

$$
\|x-a\|=2\|x-b\|\quad\Longleftrightarrow\quad\|x-c\|=r
$$

for every $x$, with $3c=4b-a$ and $3r=2\|b-a\|$.

**Correction.** The unrestricted positive-radius claim is false when $a=b$. The valid construction in every dimension, including dimension zero, is

$$
c=\frac{4b-a}{3},\qquad r=\frac{2\|b-a\|}{3}\ge0.
$$

It gives the stated equivalence for every $x$. If $a\ne b$, then $r>0$. If $a=b$, the locus is exactly $\{a\}$, with $c=a,r=0$, and it cannot equal a positive-radius sphere about any center.

**Proof.** Expanding squared Euclidean norms gives

$$
\|x-a\|^2-4\|x-b\|^2=-3\bigl(\|x-c\|^2-r^2\bigr).
$$

Thus the two squared distance equations are equivalent. All distances and $r$ are nonnegative, so the unsquared equations are equivalent as well. When $a\ne b$, $\|b-a\|>0$, proving positivity.

When $a=b$, the equation $\|x-a\|=2\|x-a\|$ forces $x=a$. Suppose this singleton were a sphere with center $c$ and radius $r>0$. Since $a$ lies on it, its reflection $2c-a$ also lies on it, because $\|(2c-a)-c\|=\|a-c\|$. The singleton condition forces $2c-a=a$, hence $c=a$, which would give $r=0$, a contradiction. In particular, $a=b=0$ in $\mathbb R^1$ is an explicit counterexample to the original universal claim.

**Lean declarations:** `exercise19`, `exercise19_original_counterexample`, `exercise19_nondegenerate`, `exercise19_degenerate_no_positive_radius`, `exercise19_degenerate`.

<a id="r01e20"></a>
### 1.20 — Dedekind cuts with greatest elements allowed
**Lean source:** [Exercise20.lean](../../Math/Rudin/Chapter01/Exercise20.lean).
**Inventory status:** Verified as stated.

**Statement.** Let a modified cut be a nonempty proper subset $A\subset\mathbb Q$ such that $p\in A$ and $q<p$ imply $q\in A$. Greatest elements are allowed. Order these cuts by strict inclusion, and define addition by the exact set of pairwise sums:

$$
A+B=\{r+s:r\in A,\ s\in B\}.
$$

These cuts are linearly ordered and have the least-upper-bound property. Addition satisfies A1–A4: closure, commutativity, associativity, and an additive identity. The identity is $Z=\{q\in\mathbb Q:q\le0\}$, which has greatest element $0$. A5 fails: the cut $N=\{q\in\mathbb Q:q<0\}$ has no additive inverse relative to $Z$.

**Proof.** First, if $r\in A$ and $s\notin A$, then $r<s$, since otherwise downward closure would imply $s\in A$. If $A\not\subseteq B$, choose $r\in A\setminus B$. Every $s\in B$ satisfies $s<r$, so $s\in A$. Hence $B\subseteq A$. Inclusion is reflexive, antisymmetric, and transitive; this comparability gives a linear order and trichotomy for strict inclusion.

Let $\mathcal A$ be a nonempty family of cuts bounded above by a cut $B$. Its union $U=\bigcup_{A\in\mathcal A}A$ is nonempty and downward closed. It is contained in $B$, so it is proper. Every member of $\mathcal A$ is contained in $U$, and every upper bound of the family contains $U$. Thus $U$ is its least upper bound, with membership exactly $q\in U$ if and only if $q\in A$ for some $A\in\mathcal A$.

For closure under addition, choose elements of $A$ and $B$ to obtain an element of $A+B$. Choose $r'\notin A$ and $s'\notin B$. Every sum $r+s\in A+B$ satisfies $r+s<r'+s'$, so $r'+s'\notin A+B$ and the sum is proper. If $q\le r+s$, then $q-s\le r$, so $q-s\in A$ and $q=(q-s)+s\in A+B$. Thus it is a modified cut; no extra closure points are added.

Commutativity follows from $r+s=s+r$. Associativity follows because both $(A+B)+C$ and $A+(B+C)$ consist exactly of the sums $r+s+t$ with $r\in A,s\in B,t\in C$. For the identity, $r\in A$ and $s\le0$ imply $r+s\in A$, while each $r\in A$ equals $r+0$. Hence $A+Z=A$, and commutativity gives $Z+A=A$.

Finally, suppose $N+B=Z$. Since $0\in Z$, there are $r<0$ and $s\in B$ with $r+s=0$. But $r/2<0$, so $r/2+s\in N+B$. This number equals $-r/2>0$, contradicting membership in $Z$. Thus $N$ has no inverse, and the universal inverse axiom fails.

**Lean declarations:** `exercise20_order`, `exercise20_cut_properties`, `exercise20_least_upper_bounds`, `exercise20_union_isLUB`, `exercise20_addition_closed`, `exercise20_mem_add`, `exercise20_addition_commutative`, `exercise20_addition_associative`, `exercise20_zero`, `exercise20_zero_has_greatest`, `exercise20_inverse_failure`, `exercise20_not_A5`.

<a id="chapter-02"></a>

## Chapter 2 — Basic Topology

**Exercises:** [1](#r02e01) · [2](#r02e02) · [3](#r02e03) · [4](#r02e04) · [5](#r02e05) · [6](#r02e06) · [7](#r02e07) · [8](#r02e08) · [9](#r02e09) · [10](#r02e10) · [11](#r02e11) · [12](#r02e12) · [13](#r02e13) · [14](#r02e14) · [15](#r02e15) · [16](#r02e16) · [17](#r02e17) · [18](#r02e18) · [19](#r02e19) · [20](#r02e20) · [21](#r02e21) · [22](#r02e22) · [23](#r02e23) · [24](#r02e24) · [25](#r02e25) · [26](#r02e26) · [27](#r02e27) · [28](#r02e28) · [29](#r02e29) · [30](#r02e30)

<a id="r02e01"></a>
### 2.1 — The empty subset
**Lean source:** [Exercise01.lean](../../Math/Rudin/Chapter02/Exercise01.lean).
**Inventory status:** Verified as stated.

**Statement.** For every set $A$ in any ambient set, $\varnothing\subseteq A$.

**Proof.** The assertion requires that each member of $\varnothing$ belong to $A$. There is no member of $\varnothing$, so the implication holds.

**Lean declarations:** `exercise01`.

<a id="r02e02"></a>
### 2.2 — Countably infinitely many algebraic numbers
**Lean source:** [Exercise02.lean](../../Math/Rudin/Chapter02/Exercise02.lean).
**Inventory status:** Verified as stated.

**Statement.** A complex number is algebraic if it is a root of a nonzero polynomial with integer coefficients. The set of algebraic complex numbers is countably infinite. In a displayed finite coefficient list, the coefficients must not all vanish; the coefficient at the last displayed index need not be nonzero.

**Proof.** Integer polynomials form an at most countable set: each is specified by a finite list of integers. Each nonzero polynomial has finitely many complex roots. Thus the algebraic numbers form a countable union of finite sets and are at most countable. For every $n\in\mathbb N$, the polynomial $X-n$ is nonzero and has root $n$. These roots are distinct, so the set is infinite.

**Lean declarations:** `exercise02`.

<a id="r02e03"></a>
### 2.3 — A transcendental real number exists
**Lean source:** [Exercise03.lean](../../Math/Rudin/Chapter02/Exercise03.lean).
**Inventory status:** Verified as stated.

**Statement.** There exists $x\in\mathbb R$ such that $p(x)\ne0$ for every nonzero $p\in\mathbb Z[X]$.

**Proof.** There are at most countably many integer polynomials, and each nonzero polynomial has finitely many real roots. Their real roots therefore form an at most countable set. Since $\mathbb R$ is uncountable, some real number lies outside this set. It satisfies the required condition.

**Lean declarations:** `exercise03`.

<a id="r02e04"></a>
### 2.4 — Irrational numbers are uncountable
**Lean source:** [Exercise04.lean](../../Math/Rudin/Chapter02/Exercise04.lean).
**Inventory status:** Verified as stated.

**Statement.** The set $\mathbb R\setminus\mathbb Q$ is uncountable.

**Proof.** The rational numbers are countable. If the irrational numbers were at most countable, their union with the rationals would make $\mathbb R$ at most countable. This contradicts the uncountability of $\mathbb R$.

**Lean declarations:** `exercise04`.

<a id="r02e05"></a>
### 2.5 — Exactly three accumulation points
**Lean source:** [Exercise05.lean](../../Math/Rudin/Chapter02/Exercise05.lean).
**Inventory status:** Verified as stated.

**Statement.** The bounded set

$$
E=\{1/n:n\ge1\}\cup\{2+1/n:n\ge1\}\cup\{4+1/n:n\ge1\},
$$

where $n$ is an integer, has derived set $E'=\{0,2,4\}$, which has exactly three elements.

**Proof.** Each term lies in $[0,5]$, so $E$ is bounded. For each $a\in\{0,2,4\}$, the distinct points $a+1/n$ converge to $a$, making $a$ an accumulation point. No other point is an accumulation point of this sequence: a neighborhood separated from its limit meets only finitely many terms, and a smaller punctured neighborhood avoids those terms. The derived set of a finite union is the union of its derived sets. Indeed, a point outside all these derived sets has a punctured neighborhood avoiding each set, and the finite intersection of those neighborhoods avoids the union. Thus $E'=\{0,2,4\}$; these three real numbers are distinct.

**Lean declarations:** `exercise05`.

<a id="r02e06"></a>
### 2.6 — Derived sets and closure
**Lean source:** [Exercise06.lean](../../Math/Rudin/Chapter02/Exercise06.lean).
**Inventory status:** Verified as stated.

**Statement.** For a subset $E$ of a metric space, its derived set $E'$ is closed, and

$$
\overline E=E\cup E',\qquad (\overline E)'=E'.
$$

However, $E$ and $E'$ need not have the same accumulation points.

**Proof.** If $x\notin E'$, choose $r>0$ such that $B(x,r)\cap E\subseteq\{x\}$. Every $y\in B(x,r)$ distinct from $x$ has a small ball contained in $B(x,r)$ and avoiding $x$, hence avoiding $E$. Neither such a $y$ nor $x$ belongs to $E'$. Thus the complement of $E'$ is open, and $E'$ is closed.

A point of $\overline E$ either belongs to $E$ or has another point of $E$ in each neighborhood. This proves $\overline E=E\cup E'$. Monotonicity gives $E'\subseteq(\overline E)'$. For the reverse inclusion, if $x\notin E'$, choose the ball above. Every other point of that ball has a neighborhood disjoint from $E$, so $B(x,r)\cap\overline E\subseteq\{x\}$. Hence $x\notin(\overline E)'$.

For a counterexample, take $E=\{1/n:n\ge1\}\subset\mathbb R$. Its only accumulation point is $0$, so $E'=\{0\}$. A finite set has no accumulation points, giving $(E')'=\varnothing\ne E'$.

**Lean declarations:** `exercise06_derived_closed`, `exercise06_closure_limit_points`, `exercise06_derived_limit_points`, `exercise06_counterexample`.

<a id="r02e07"></a>
### 2.7 — Closure of finite and countable unions
**Lean source:** [Exercise07.lean](../../Math/Rudin/Chapter02/Exercise07.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $A_i$ be subsets of a metric space. For every integer $n\ge0$,

$$
\overline{\bigcup_{i=1}^{n}A_i}=\bigcup_{i=1}^{n}\overline{A_i}.
$$

For the countable union,

$$
\bigcup_{i=1}^{\infty}\overline{A_i}\subseteq
\overline{\bigcup_{i=1}^{\infty}A_i},
$$

and strict containment can occur.

**Proof.** Each $A_i$ lies in the union, so monotonicity of closure gives the inclusion from the union of closures into the closure of the union. For a finite family, the union of the closures is closed and contains every $A_i$, so it also contains the closure of their union. When $n=0$, both sets are empty.

For strictness, put $A_i=\{1/i\}\subset\mathbb R$ for $i\ge1$. Each singleton is closed, so the union of their closures does not contain $0$. But $1/i\to0$, so $0$ belongs to the closure of their union.

**Lean declarations:** `exercise07a`, `exercise07b_inclusion`, `exercise07b_strict`.

<a id="r02e08"></a>
### 2.8 — Accumulation points of open and closed plane sets
**Lean source:** [Exercise08.lean](../../Math/Rudin/Chapter02/Exercise08.lean).
**Inventory status:** Verified as stated.

**Statement.** Every member of an open subset of Euclidean $\mathbb R^2$ is an accumulation point of that set. This assertion is false for closed subsets.

**Proof.** If $x\in E$ and $E$ is open, some ball $B(x,r)$ lies in $E$. Every neighborhood of $x$ contains a point on a sufficiently short, nonzero line segment from $x$ inside that ball. Thus it contains a point of $E$ other than $x$. In contrast, $E=\{(0,0)\}$ is closed, contains the origin, and has no point different from the origin. The origin is not an accumulation point.

**Lean declarations:** `exercise08_open`, `exercise08_closed`.

<a id="r02e09"></a>
### 2.9 — Interior and its limits
**Lean source:** [Exercise09.lean](../../Math/Rudin/Chapter02/Exercise09.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $E$ be a subset of a metric space $X$, and write $E^\circ$ for its interior.

1. $E^\circ$ is open.
2. $E$ is open if and only if $E^\circ=E$.
3. If $G$ is open and $G\subseteq E$, then $G\subseteq E^\circ$.
4. $X\setminus E^\circ=\overline{X\setminus E}$.
5. $E^\circ$ need not equal $(\overline E)^\circ$.
6. $\overline E$ need not equal $\overline{E^\circ}$.

**Proof.** The interior is the union of all open subsets of $E$. Unions of open sets are open, proving the first assertion, and every open subset of $E$ lies in this union, proving the third. If $E$ is open, it is one of those subsets, so $E^\circ=E$. Conversely, equality with the open set $E^\circ$ makes $E$ open.

A point lies outside $E^\circ$ exactly when every neighborhood meets $X\setminus E$. This is the definition of membership in $\overline{X\setminus E}$ and proves the fourth assertion.

For the fifth, take $E=\mathbb R\setminus\{0\}$. It is open and dense, so $E^\circ=E$ whereas $(\overline E)^\circ=\mathbb R$. For the sixth, take $E=\{0\}\subset\mathbb R$. Its closure is itself, but its interior and the closure of its interior are empty.

**Lean declarations:** `exercise09a`, `exercise09b`, `exercise09c`, `exercise09d`, `exercise09e`, `exercise09f`.

<a id="r02e10"></a>
### 2.10 — The zero-one metric
**Lean source:** [Exercise10.lean](../../Math/Rudin/Chapter02/Exercise10.lean).
**Inventory status:** Verified as stated.

**Statement.** On an infinite set $X$, define $d(x,y)=0$ if $x=y$, and $d(x,y)=1$ otherwise. This is a metric. Every subset is open and closed, and a subset is compact if and only if it is finite, including the empty set. The same conclusions hold without the assumption that $X$ is infinite.

**Proof.** Nonnegativity, symmetry, and $d(x,y)=0\iff x=y$ follow from the definition. If $x=z$, the triangle inequality is immediate. If $x\ne z$, at least one of $x\ne y$ and $y\ne z$ holds, so $1=d(x,z)\le d(x,y)+d(y,z)$.

Since $B(x,1/2)=\{x\}$, all singletons are open. Every set is a union of singletons and is therefore open; its complement is open as well, so it is closed. A finite set is compact by choosing one cover member for each point. For an infinite set, the cover by its open singletons has no finite subcover. The empty set has the empty finite subcover.

**Lean declarations:** `zeroOneDistance_metric_axioms`, `zeroOne_isOpen`, `zeroOne_isClosed`, `zeroOne_isCompact_iff`.

<a id="r02e11"></a>
### 2.11 — Five proposed metrics on the real line
**Lean source:** [Exercise11.lean](../../Math/Rudin/Chapter02/Exercise11.lean).
**Inventory status:** Verified as stated.

**Statement.** For $x,y\in\mathbb R$, consider

$$
\begin{aligned}
d_1(x,y)&=(x-y)^2,&d_2(x,y)&=\sqrt{|x-y|},\\
d_3(x,y)&=|x^2-y^2|,&d_4(x,y)&=|x-2y|,\\
d_5(x,y)&=\frac{|x-y|}{1+|x-y|}.
\end{aligned}
$$

Exactly $d_2$ and $d_5$ are metrics.

**Proof.** For $d_1$, the triangle inequality fails because $d_1(0,2)=4>1+1=d_1(0,1)+d_1(1,2)$. For $d_3$, separation fails: $1\ne-1$ but $d_3(1,-1)=0$. For $d_4$, both the diagonal and symmetry axioms fail: $d_4(1,1)=1\ne0$, while $d_4(0,1)=2\ne1=d_4(1,0)$.

Both $d_2$ and $d_5$ are nonnegative, symmetric, and vanish exactly when $x=y$. To prove their triangle inequalities, put $a=|x-y|$, $b=|y-z|$, and $c=|x-z|$. Then $a,b,c\ge0$ and $c\le a+b$. Since

$$
(\sqrt a+\sqrt b)^2=a+b+2\sqrt{ab}\ge c,
$$

comparison of nonnegative square roots proves the inequality for $d_2$. For $d_5$, positive denominators give

$$
\frac{c}{1+c}\le\frac{a+b}{1+a+b}
=\frac a{1+a+b}+\frac b{1+a+b}
\le\frac a{1+a}+\frac b{1+b}.
$$

Thus both positive cases satisfy all metric axioms.

**Lean declarations:** `distanceOne_not_metric`, `distanceOne_triangle_failure`, `distanceTwo_metric`, `distanceThree_not_metric`, `distanceThree_separation_failure`, `distanceFour_not_metric`, `distanceFour_diagonal_failure`, `distanceFour_symmetry_failure`, `distanceFive_metric`, `exercise11`.

<a id="r02e12"></a>
### 2.12 — Direct compactness of a sequence and its limit
**Lean source:** [Exercise12.lean](../../Math/Rudin/Chapter02/Exercise12.lean).
**Inventory status:** Verified as stated.

**Statement.** The set

$$
K=\{0\}\cup\{1/n:n\ge1\}\subset\mathbb R
$$

is compact. More explicitly, every indexed open cover of $K$ has a finite subcover, without using the Heine–Borel theorem.

**Proof.** Let $(U_i)_{i\in I}$ be an open cover. Choose $i_0$ with $0\in U_{i_0}$. Since $1/n\to0$, there is $N\ge1$ such that $1/n\in U_{i_0}$ whenever $n\ge N$. For each of the finitely many remaining terms, choose one cover member containing it. Those finitely many members together with $U_{i_0}$ cover $K$. This is the open-cover definition of compactness.

The same argument applies to a sequence together with its limit in any topological space. For this particular sequence, $K$ is countably infinite and $K'=\{0\}$: the reciprocals are distinct and positive, converge to $0$, and any point different from $0$ has a neighborhood meeting only finitely many of them. Adding the singleton $\{0\}$ creates no further accumulation point.

**Lean declarations:** `reciprocalSet_finite_subcover`, `exercise12`.

<a id="r02e13"></a>
### 2.13 — A compact set with countably infinite derived set
**Lean source:** [Exercise13.lean](../../Math/Rudin/Chapter02/Exercise13.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $A=\{0\}\cup\{1/n:n\ge1\}$ and

$$
K=A+A=\{a+b:a,b\in A\}.
$$

Then $K$ is compact and $K'=A$. In particular, its set of accumulation points is countably infinite, not merely at most countable.

**Proof.** By Exercise 2.12, $A$ is compact. The addition map is continuous on the compact product $A\times A$, so its image $K$ is compact. If $a\in A$, the points $a+1/n\in K$ differ from $a$ and converge to $a$. Thus $A\subseteq K'$.

Conversely, let $x\in K'$. Choose a sequence $u_j\in K\setminus\{x\}$ converging to $x$, and write $u_j=a_j+b_j$ with $a_j,b_j\in A$. Compactness of $A\times A$ gives a subsequence for which $(a_j,b_j)\to(a,b)\in A\times A$. Continuity and uniqueness of limits give $x=a+b$. Every nonzero point of $A$ is isolated in $A$. Thus if both $a$ and $b$ were nonzero, both summand sequences would eventually be constant, making $u_j=x$, a contradiction. One of $a,b$ is zero, so $x\in A$. This proves $K'=A$, and $A$ is countably infinite.

**Lean declarations:** `exercise13`.

<a id="r02e14"></a>
### 2.14 — An open cover without a finite subcover
**Lean source:** [Exercise14.lean](../../Math/Rudin/Chapter02/Exercise14.lean).
**Inventory status:** Verified as stated.

**Statement.** The family $U_t=(t,\infty)$, indexed by all positive real numbers $t$, covers $(0,1)$, but no finite subfamily covers $(0,1)$.

**Proof.** Each $U_t$ is open. If $0<x<1$, then $t=x/2>0$ and $x\in U_t$, proving coverage. Given a nonempty finite set of positive indices, let $m$ be its minimum and take $x=\min(1,m)/2$. Then $0<x<1$ and $x<t$ for every selected index, so $x$ lies in none of the selected rays. The empty subfamily also fails to cover, for example because it misses $1/2$.

**Lean declarations:** `exercise14`.

<a id="r02e15"></a>
### 2.15 — Closedness or boundedness alone is insufficient
**Lean source:** [Exercise15.lean](../../Math/Rudin/Chapter02/Exercise15.lean).
**Inventory status:** Verified as stated.

**Statement.** The compact-set finite-intersection theorem and its decreasing-sequence corollary both fail if compactness is replaced by closedness alone. They also both fail if it is replaced by boundedness alone.

**Proof.** For $n\ge0$, let $F_n=[n,\infty)\subset\mathbb R$. These sets are closed, nonempty, and decreasing. Every nonempty finite intersection equals the member with largest index and is therefore nonempty; the intersection of the empty family is $\mathbb R$. However, no real number is at least every natural number, so $\bigcap_{n\ge0}F_n=\varnothing$. This gives both closed-set counterexamples.

For the bounded-set counterexamples, let $B_n=(0,1/(n+1))$. These sets are bounded, nonempty, and decreasing. Their finite intersections are nonempty by the same largest-index argument, including the empty family as above. A member of their total intersection would be positive and less than $1/(n+1)$ for every $n$, which contradicts $1/(n+1)\to0$. Thus the total intersection is empty. These are separate replacements of compactness, not a counterexample under joint closedness and boundedness in $\mathbb R$.

**Lean declarations:** `closed_finite_intersection_counterexample`, `closed_nested_counterexample`, `bounded_finite_intersection_counterexample`, `bounded_nested_counterexample`.

<a id="r02e16"></a>
### 2.16 — A clopen bounded noncompact subset of the rationals
**Lean source:** [Exercise16.lean](../../Math/Rudin/Chapter02/Exercise16.lean).
**Inventory status:** Verified as stated.

**Statement.** In $\mathbb Q$ with its usual metric, the set

$$
E=\{q\in\mathbb Q:2<q^2<3\}
$$

is closed and bounded but not compact. It is also open in $\mathbb Q$.

**Proof.** The map $q\mapsto q^2$ is continuous, so $E$ is the inverse image of $(2,3)$ and is open. Since $\sqrt2$ and $\sqrt3$ are irrational, no rational square equals $2$ or $3$. Thus $E$ is also the inverse image of the closed interval $[2,3]$ and is closed. Its members satisfy $|q|<2$, proving boundedness.

Suppose $E$ were compact. It is nonempty because $3/2\in E$. The continuous real-valued function $q\mapsto q^2$ would attain a minimum at some $q\in E$. But $\sqrt2<|q|$, so density of the rationals gives $r\in\mathbb Q$ with $\sqrt2<r<|q|$. Consequently $2<r^2<q^2<3$, so $r\in E$ has a smaller square, a contradiction. All topological claims here are relative to $\mathbb Q$.

**Lean declarations:** `rationalSquareBand_isClosed`, `rationalSquareBand_isBounded`, `rationalSquareBand_not_isCompact`, `rationalSquareBand_isOpen`, `exercise16`.

<a id="r02e17"></a>
### 2.17 — Decimal expansions using only 4 and 7
**Lean source:** [Exercise17.lean](../../Math/Rudin/Chapter02/Exercise17.lean).
**Inventory status:** Verified as stated.

**Statement.** Let

$$
E=\left\{\sum_{n=0}^{\infty}\frac{d_n}{10^{n+1}}:d_n\in\{4,7\}\right\}\subseteq[0,1].
$$

Then $E$ is uncountable, is not dense in $[0,1]$, is compact, and is perfect: it is closed and every member is an accumulation point. Each permitted expansion is unique even among expansions using all ten decimal digits.

**Proof.** Encode digits by binary sequences, with $0$ selecting $4$ and $1$ selecting $7$. This defines a continuous map $f:\{0,1\}^{\mathbb N}\to\mathbb R$: agreement through the first $N$ digits bounds the remaining difference by a geometric tail tending to zero. Its image is exactly $E$. The binary sequence space is compact, so $E$ is compact and therefore closed.

To check uniqueness, every tail consisting of digits $4$ and $7$ has decimal value strictly between $0$ and $1$. If such an expansion and any other decimal expansion first differed at position $n$, cancellation of the common prefix and multiplication by $10^{n+1}$ would give

$$
d_n+u=e_n+v,\qquad 0<u<1,\quad 0\le v\le1.
$$

If $d_n>e_n$, the left side exceeds $e_n+1$; if $d_n<e_n$, it is less than $e_n$. Both contradict the equality. Thus no position differs. In particular, $f$ is injective, and terminating-versus-repeating-nine ambiguity cannot affect $E$.

Binary sequence space is uncountable by Cantor's diagonal argument: from a purported enumeration $a^{(n)}$, the sequence whose $n$th bit is the opposite of $a^{(n)}_n$ is omitted. Injectivity of $f$ makes $E$ uncountable. For any permitted digit sequence, change just its $n$th digit. The resulting values differ from the original value and converge to it as $n\to\infty$. Thus there are no isolated points. Finally, the first digit gives $x\ge4/10$ for all $x\in E$. Since $E$ is closed, $0\notin\overline E$, although $0\in[0,1]$. Equivalently, the relatively open neighborhood $[0,4/10)$ is disjoint from $E$, so density also fails in the subspace topology of $[0,1]$.

**Lean declarations:** `decimal47Set_not_countable`, `decimal47Set_not_dense`, `decimal47Set_not_dense_subspace`, `decimal47Set_isCompact`, `decimal47Set_perfect`, `decimal47Set_isClosed`, `decimal47Set_no_isolated`.

<a id="r02e18"></a>
### 2.18 — A perfect set containing only irrational numbers
**Lean source:** [Exercise18.lean](../../Math/Rudin/Chapter02/Exercise18.lean).
**Inventory status:** Verified as stated.

**Statement.** There exists a nonempty compact perfect set $P\subset\mathbb R$ with $P\cap\mathbb Q=\varnothing$. In particular, a nonempty closed set with no isolated points can contain no rational number.

**Proof.** The source uses standard Polish-space results. First, $\mathbb R\setminus\mathbb Q$ is uncountable, because otherwise its union with the countable set $\mathbb Q$ would make $\mathbb R$ countable. Since $\mathbb Q$ is Borel, the Polish topology refinement theorem supplies a finer Polish topology on $\mathbb R$ in which its complement is closed. The perfect-set theorem for uncountable closed subsets of Polish spaces then gives a continuous injection

$$
f:\{0,1\}^{\mathbb N}\longrightarrow\mathbb R\setminus\mathbb Q
$$

for that finer topology. The identity map from the finer topology to the usual topology is continuous, so $f$ is also continuous as an ordinary real-valued map.

Set $P=f(\{0,1\}^{\mathbb N})$. Its domain is nonempty and compact, so $P$ is nonempty and compact in the usual real topology, hence closed. To show that $f(a)$ is not isolated, flip only the $n$th bit of $a$. These distinct sequences converge to $a$ in the product topology; continuity gives convergence of their images to $f(a)$, and injectivity makes all those images different from $f(a)$. Thus $P$ is perfect. Its construction places every member outside $\mathbb Q$. The finer topology is only a proof tool; every stated property of $P$ uses the usual topology.

**Lean declarations:** `exists_nonempty_perfect_irrational_set`.

<a id="r02e19"></a>
### 2.19 — Separation and uncountability of connected spaces
**Lean source:** [Exercise19.lean](../../Math/Rudin/Chapter02/Exercise19.lean).
**Inventory status:** Verified as stated.

**Statement.** Subsets $A,B$ of a metric space are *separated* when

$$
\overline A\cap B=\varnothing,\qquad A\cap\overline B=\varnothing.
$$

This does not require disjoint closures or positive distance.

1. Disjoint closed sets are separated.
2. Disjoint open sets are separated.
3. For $p\in X$ and $\delta>0$, the sets $\{q:d(p,q)<\delta\}$ and $\{q:d(p,q)>\delta\}$ are separated. The Lean result holds for every real $\delta$.
4. A connected metric space with two distinct points is uncountable.

**Proof.** For closed sets, replace each closure by the set itself. If $A$ and $B$ are disjoint and open, a point of $B$ has the neighborhood $B$ disjoint from $A$, so it cannot belong to $\overline A$; the other condition follows symmetrically. The two sets in the third assertion are disjoint and open by continuity of $q\mapsto d(p,q)$, so the second assertion applies for every $\delta$.

For the fourth, let $a\ne b$. The continuous image of $X$ under $x\mapsto d(a,x)$ is connected and contains both $0$ and $d(a,b)>0$. A connected subset of the real line contains the interval between any two of its points, so the image contains $[0,d(a,b)]$. That nondegenerate interval is uncountable. If $X$ were at most countable, its image would be at most countable, a contradiction.

**Lean declarations:** `exercise19_a`, `exercise19_b`, `exercise19_c`, `exercise19_d`.

<a id="r02e20"></a>
### 2.20 — Connected closure and disconnected interior
**Lean source:** [Exercise20.lean](../../Math/Rudin/Chapter02/Exercise20.lean).
**Inventory status:** Verified as stated.

**Statement.** The closure of a connected set is connected. This holds in every topological space, with the empty set allowed as connected in Rudin's convention. The interior of a connected set need not be connected, even in $\mathbb R^2$.

**Proof.** A dense connected subset of a space forces that space to be connected: any separation of the space into two nonempty relatively open sets meets the dense subset on both sides and would separate it. Apply this observation to $E\subseteq\overline E$. The empty case has empty closure.

For the interior, take

$$
S=\{(x,y)\in\mathbb R^2:x\ne0\}\cup\{(0,0)\}.
$$

For every $p\in S$, the segment from the origin to $p$ lies in $S$: a positive multiple of a point with nonzero first coordinate still has nonzero first coordinate, and the zero multiple is the origin. Hence $S$ is star-convex, thus path connected and connected. Its interior is exactly $\{(x,y):x\ne0\}$. That set is open, while the added origin is not interior because every ball about it contains a nonzero point on the vertical axis, outside $S$. The interior is the disjoint union of the two nonempty open half-planes $x<0$ and $x>0$, so it is disconnected.

**Lean declarations:** `exercise20_closure_connected`, `exercise20_interior_counterexample`.

<a id="r02e21"></a>
### 2.21 — Separated sets and line segments
**Lean source:** [Exercise21.lean](../../Math/Rudin/Chapter02/Exercise21.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $A,B\subseteq\mathbb R^k$ be separated, and define $p(t)=(1-t)a+tb$ for all real $t$.

1. For any $a,b\in\mathbb R^k$, the preimages $A_0=p^{-1}(A)$ and $B_0=p^{-1}(B)$ are separated subsets of $\mathbb R$.
2. If $a\in A$ and $b\in B$, some $t_0\in(0,1)$ satisfies $p(t_0)\notin A\cup B$.
3. Every convex subset of $\mathbb R^k$ is connected, including the empty set. The results allow $k=0$.

**Proof.** The map $p$ is continuous. For any set $D$, continuity gives $\overline{p^{-1}(D)}\subseteq p^{-1}(\overline D)$. Applying this to $A$ and $B$, the two separation conditions pull back to give the first assertion.

For the second, suppose the entire segment $C=p([0,1])$ lay in $A\cup B$. It is connected as the continuous image of $[0,1]$ and meets both $A$ and $B$. The sets $C\cap A$ and $C\cap B$ are disjoint and nonempty. They are relatively closed in $C$: for example, $C\cap\overline A=C\cap A$, since no point of $B$ lies in $\overline A$. They therefore separate $C$, a contradiction. Some segment point is outside $A\cup B$, and it cannot be either endpoint, so its parameter lies strictly between $0$ and $1$.

If a convex set had a separation into two nonempty parts, choose one point in each. Convexity puts the whole segment between them in the set, contrary to the second assertion. Hence it is connected; the empty case has no such separation.

**Lean declarations:** `exercise21_a`, `exercise21_b`, `exercise21_c`.

<a id="r02e22"></a>
### 2.22 — Rational coordinates give separability
**Lean source:** [Exercise22.lean](../../Math/Rudin/Chapter02/Exercise22.lean).
**Inventory status:** Verified as stated.

**Statement.** Euclidean $\mathbb R^k$ has the at most countable dense subset $\mathbb Q^k$. This proves separability for positive integers $k$ and also for $k=0$.

**Proof.** A finite product of countable sets is countable, so the rational-coordinate points are at most countable. For $k>0$, given $x\in\mathbb R^k$ and $\varepsilon>0$, choose rational $q_i$ with $|q_i-x_i|<\varepsilon/\sqrt{k}$ for each coordinate. Then

$$
\|q-x\|_2^2=\sum_{i=1}^{k}|q_i-x_i|^2<\varepsilon^2,
$$

so every ball meets $\mathbb Q^k$. Equivalently, this is density of the finite product of the dense rational subsets, under the usual product–Euclidean homeomorphism used in Lean. For $k=0$, the Euclidean space and its rational-coordinate subset each consist of the single empty tuple.

**Lean declarations:** `exercise22_countable`, `exercise22_dense`, `exercise22`.

<a id="r02e23"></a>
### 2.23 — A countable base from a dense set
**Lean source:** [Exercise23.lean](../../Math/Rudin/Chapter02/Exercise23.lean).
**Inventory status:** Verified as stated.

**Statement.** If a metric space $X$ has an at most countable dense subset $D$, then it has an at most countable family $\mathcal B$ of open sets such that, for every open $G$ and $x\in G$, some $V\in\mathcal B$ satisfies $x\in V\subseteq G$. Finite and empty spaces are included.

**Proof.** This is the standard theorem that a separable metric space is second countable, used in Lean. Explicitly, take all balls $B(d,r)$ with $d\in D$ and positive rational $r$. They form an at most countable family of open sets. Given $x\in G$, choose $\varepsilon>0$ with $B(x,\varepsilon)\subseteq G$. Density gives $d\in D$ with $d(x,d)<\varepsilon/3$. Choose a rational radius with

$$
d(x,d)<r<\varepsilon-d(x,d).
$$

Then $x\in B(d,r)$, and the triangle inequality gives $B(d,r)\subseteq B(x,\varepsilon)\subseteq G$. If $X$ is empty, the empty family satisfies the condition vacuously.

**Lean declarations:** `exercise23`.

<a id="r02e24"></a>
### 2.24 — Accumulation points imply separability
**Lean source:** [Exercise24.lean](../../Math/Rudin/Chapter02/Exercise24.lean).
**Inventory status:** Verified as stated.

**Statement.** Suppose that every infinite subset $E$ of a metric space $X$ has an accumulation point in $X$. Then $X$ has an at most countable dense subset. No infinitude or nonemptiness assumption on $X$ is needed.

**Proof.** The source first proves a stronger intermediate result: $X$ is compact. It uses the standard characterization of countable compactness by accumulation points of infinite subsets, followed by the metric-space implications from countable compactness to sequential compactness and from sequential compactness to compactness. These theorems apply to the stated hypothesis without a nonemptiness assumption.

To see how compactness gives the conclusion, for each $n\ge1$ choose a finite subcover from the cover by balls of radius $1/n$, and let $D_n$ be their centers. The set $D=\bigcup_{n\ge1}D_n$ is at most countable. Given a nonempty ball $B(x,\varepsilon)$, choose $n$ with $1/n<\varepsilon$. Some selected center lies within $1/n$ of $x$, hence in that ball. Thus $D$ is dense. In the empty space, all the finite center sets can be empty. The Lean proof uses these compactness equivalences rather than the exercise's suggested separated-point construction.

**Lean declarations:** `compact_of_infinite_accumulation`, `exercise24`.

<a id="r02e25"></a>
### 2.25 — Compact metric spaces are separable and second countable
**Lean source:** [Exercise25.lean](../../Math/Rudin/Chapter02/Exercise25.lean).
**Inventory status:** Verified as stated.

**Statement.** Every compact metric space $X$ has an at most countable dense subset and an at most countable base of open sets. The base refines every open neighborhood: if $x\in G$ and $G$ is open, some base member $V$ satisfies $x\in V\subseteq G$.

**Proof.** For each positive integer $n$, compactness selects finitely many radius-$1/n$ balls covering $X$. The union of their centers over all $n$ is at most countable and dense: for any $x$ and any $\varepsilon>0$, a selected center is within $1/n<\varepsilon$ of $x$ for sufficiently large $n$. Apply Exercise 2.23 to this dense subset to obtain the base and its refinement property. For the empty space, both the dense set and the base may be empty; finite spaces are also included.

**Lean declarations:** `exercise25_base`, `exercise25_separable`.

<a id="r02e26"></a>
### 2.26 — Accumulation points imply the finite-subcover property
**Lean source:** [Exercise26.lean](../../Math/Rudin/Chapter02/Exercise26.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $X$ be a metric space in which every infinite subset has an accumulation point in $X$. For any index set $I$ and any open cover $(U_i)_{i\in I}$ of $X$, there is a finite $J\subseteq I$ with $X\subseteq\bigcup_{i\in J}U_i$.

**Proof.** As established in Exercise 2.24, the accumulation-point hypothesis implies countable compactness, hence sequential compactness and compactness in a metric space. Apply the defining finite-subcover property of compactness to the given indexed cover. The cover need not be countable. If $X=\varnothing$, choose $J=\varnothing$. Thus the assertion also includes empty and finite spaces.

**Lean declarations:** `exercise26`.

<a id="r02e27"></a>
### 2.27 — Condensation points and the countable remainder
**Lean source:** [Exercise27.lean](../../Math/Rudin/Chapter02/Exercise27.lean).
**Inventory status:** Verified as stated.

**Statement.** For an uncountable set $E\subseteq\mathbb R^k$, define

$$
P=\{x:\text{every open neighborhood }U\text{ of }x\text{ meets }E\text{ uncountably}\}.
$$

Then $P$ is perfect and $E\setminus P$ is at most countable. A condensation point is not required to belong to $E$. The Lean results establish closedness and absence of isolated points for this $P$, and countability of the remainder, for every subset of any second-countable topological space, without assuming $E$ uncountable.

**Proof.** If $x\notin P$, some open neighborhood $U$ has $U\cap E$ at most countable. The same $U$ shows that every point of $U$ lies outside $P$. Thus $P$ is closed.

Choose a countable base $\mathcal B$. Each $x\in E\setminus P$ belongs to a base member $V$ contained in an open neighborhood whose intersection with $E$ is at most countable. Consequently

$$
E\setminus P\subseteq
\bigcup_{\substack{V\in\mathcal B\\V\cap E\text{ at most countable}}}(V\cap E).
$$

This is a countable union of at most countable sets, so the remainder is at most countable.

If $x\in P$ were isolated in $P$, an open neighborhood $U$ of $x$ would satisfy $U\cap P\subseteq\{x\}$. It would follow that $U\cap E\subseteq(E\setminus P)\cup\{x\}$ is at most countable, contrary to the definition of $P$. Thus $P$ is perfect. For the source's uncountable $E$, the countability of $E\setminus P$ also forces $P$ to be nonempty.

**Lean declarations:** `exercise27_perfect`, `exercise27_countable`.

<a id="r02e28"></a>
### 2.28 — Perfect-set decomposition and isolated points
**Lean source:** [Exercise28.lean](../../Math/Rudin/Chapter02/Exercise28.lean).
**Inventory status:** Verified as stated.

**Statement.** Every closed subset $F$ of a separable metric space can be written

$$
F=P\cup C,
$$

where $P$ is perfect, possibly empty, and $C$ is at most countable. Every countably infinite closed subset of Euclidean $\mathbb R^k$ has an isolated point. More strongly, every nonempty at most countable closed subset of $\mathbb R^k$ has an isolated point. These Euclidean assertions allow $k=0$.

**Scope and countability convention.** Rudin uses “countable” to mean countably infinite in the source corollary. This already excludes the empty set, so the corollary is verified as stated, not refuted. If “countable” is instead translated as at most countable, nonemptiness must be stated. The empty set is closed and at most countable but has no isolated point because it has no member. This is a translation check, not a source erratum. The isolated-point corollary is not asserted for arbitrary separable metric spaces; for example, $\mathbb Q$ is closed in itself, countable, and has no isolated points.

**Proof.** A separable metric space is second countable. The Cantor–Bendixson decomposition theorem used in Lean gives the stated union. It can also be obtained from the condensation-point argument of Exercise 2.27: let $P$ be the condensation points of $F$. They form a perfect set and $F\setminus P$ is at most countable. Since $F$ is closed, every condensation point belongs to $F$; a point outside $F$ has the open neighborhood $X\setminus F$ meeting $F$ in no points. Thus $C=F\setminus P$ gives $F=P\cup C$. For $F=\varnothing$, take both parts empty.

Now let $F\subseteq\mathbb R^k$ be closed, nonempty, and at most countable. If no member were isolated, $F$ would be a nonempty perfect set. The perfect-set theorem in complete metric spaces supplies an injection of binary sequence space into $F$. Binary sequence space is uncountable by the diagonal argument, contradicting countability of $F$. Hence an isolated point exists. A countably infinite $F$ is nonempty, so the source corollary follows. The empty-set check follows directly from the impossibility of choosing $x\in\varnothing$.

**Lean declarations:** `exercise28_decomposition`, `exercise28_source`, `exercise28_empty`, `exercise28_nonempty`.

<a id="r02e29"></a>
### 2.29 — Disjoint open intervals, including unbounded components
**Lean source:** [Exercise29.lean](../../Math/Rudin/Chapter02/Exercise29.lean).
**Inventory status:** Verified refutation and correction.

**Statement.** Every open set $U\subseteq\mathbb R$ is the union of an at most countable family of pairwise disjoint nonempty open interval components. Each component has one of the forms

$$
(a,b)\quad(a<b),\qquad(a,\infty),\qquad(-\infty,b),\qquad\mathbb R,
$$

with finite real $a,b$ where applicable. The empty open set has the empty family. Each ray and the whole line has just itself as its component.

**Correction.** The source says “segments.” Definition 2.17 displays two finite real endpoints; under that bounded-only reading, the assertion is false. Later usage on book page 278 explicitly permits unbounded segments. The verified decomposition uses that extended open-interval convention. It does not silently replace finite endpoints by infinite endpoints. Separately, the Lean file proves that the connected open set $\mathbb R$ cannot be a pairwise disjoint union of bounded open segments, even without a countability restriction and even if empty segments are allowed.

**Proof.** For each $x\in U$, take its connected component $C_x$ within $U$, and retain distinct components only. Each component is nonempty and connected. It is open: every point $y$ in it has a small open interval contained in $U$; this interval is connected and meets the component, so maximality places the interval in the same component. Distinct components are disjoint, and every point of $U$ lies in its own component. Thus they cover $U$.

A connected subset of $\mathbb R$ contains every point between any two of its points. Hence each open nonempty component is an interval. If it is bounded on both sides, its infimum and supremum give $(a,b)$; if bounded on just one side, it is the corresponding open ray; if unbounded on both sides, it is $\mathbb R$. Endpoints cannot be included because the component is open. Each component contains a rational number. Choosing one rational in each gives an injection into $\mathbb Q$, because distinct components are disjoint. The family is therefore at most countable. If $U$ is empty there is no component to choose; if $U$ is a nonempty connected interval, ray, or the whole line, its only component is $U$.

For the bounded-only obstruction, suppose a pairwise disjoint family of bounded open segments covered $\mathbb R$. Choose a member $I$ containing $0$. The complement of $I$ is the union of all the other members, hence is open. Thus $I$ is a nonempty clopen subset of connected $\mathbb R$, so $I=\mathbb R$. But a bounded open segment omits its finite left endpoint and cannot be the whole line. This contradiction proves the refutation.

**Lean declarations:** `exercise29_source_segments`, `exercise29_bounded_segment_obstruction`, `exercise29_open_interval_decomposition`, `exercise29_components_empty`, `exercise29_components_Ioi`, `exercise29_components_Iio`, `exercise29_components_univ`.

<a id="r02e30"></a>
### 2.30 — Euclidean Baire theorem by nested compact balls
**Lean source:** [Exercise30.lean](../../Math/Rudin/Chapter02/Exercise30.lean).
**Inventory status:** Verified as stated.

**Statement.** In $\mathbb R^k$:

1. If $\mathbb R^k=\bigcup_{n\ge1}F_n$ and every $F_n$ is closed, some $F_n$ has nonempty interior.
2. If every $G_n$ is open and dense, then $\bigcap_{n\ge1}G_n$ is nonempty.
3. The same intersection is dense.

The Lean statements allow every nonnegative integer $k$, including $k=0$. Their zero-based indices denote the source's positive indices.

**Proof.** Let $U$ be any nonempty open subset of $\mathbb R^k$. Choose a closed ball $K_0=\overline B(c_0,r_0)\subseteq U$ with $r_0>0$. Given $K_{n-1}=\overline B(c_{n-1},r_{n-1})$, density and openness of $G_n$ make

$$
B(c_{n-1},r_{n-1})\cap G_n
$$

nonempty and open. Choose a positive-radius closed ball $K_n$ inside this intersection. Thus each $K_n$ is nonempty and closed, $K_n\subseteq K_{n-1}$, and $K_n\subseteq G_n$.

Euclidean closed balls are compact. The nested compact-set theorem gives a point $x\in\bigcap_{n\ge0}K_n$. Then $x\in U$ and $x\in G_n$ for every $n\ge1$. Since every nonempty open $U$ meets $\bigcap_{n\ge1}G_n$, the intersection is dense. Taking $U=\mathbb R^k$, which contains the zero vector even when $k=0$, proves nonemptiness. No shrinking-radius assumption is needed: compactness of the first ball and nesting suffice.

Finally, if every closed $F_n$ in the cover had empty interior, each complement $G_n=\mathbb R^k\setminus F_n$ would be open and dense. The preceding construction would give a point in all these complements, outside the supposed cover. Therefore some $F_n$ has nonempty interior. This is the requested nested-set argument, not an invocation of Baire's theorem as a black box.

**Lean declarations:** `exercise30_closed_cover`, `exercise30_open_intersection_nonempty`, `exercise30_open_intersection_dense`.

<a id="chapter-03"></a>

## Chapter 3 — Numerical Sequences and Series

**Exercises:** [1](#r03e01) · [2](#r03e02) · [3](#r03e03) · [4](#r03e04) · [5](#r03e05) · [6](#r03e06) · [7](#r03e07) · [8](#r03e08) · [9](#r03e09) · [10](#r03e10) · [11](#r03e11) · [12](#r03e12) · [13](#r03e13) · [14](#r03e14) · [15](#r03e15) · [16](#r03e16) · [17](#r03e17) · [18](#r03e18) · [19](#r03e19) · [20](#r03e20) · [21](#r03e21) · [22](#r03e22) · [23](#r03e23) · [24](#r03e24) · [25](#r03e25)

<a id="r03e01"></a>
### 3.1 — Limits of absolute values
**Lean source:** [Exercise01.lean](../../Math/Rudin/Chapter03/Exercise01.lean).
**Inventory status:** Verified as stated.

**Statement.** If a real or complex sequence $s_n$ tends to $s$, then $|s_n|\to|s|$. The converse is false. More generally, convergence in a seminormed additive group implies convergence of the norms.

**Proof.** The reverse triangle inequality gives

$$
\bigl|\|s_n\|-\|s\|\bigr|\leq\|s_n-s\|\longrightarrow0.
$$

For the converse, take $s_n=(-1)^n$. Its absolute values are all $1$, but its even and odd subsequences have the distinct limits $1$ and $-1$. Thus it has no limit.

**Lean declarations:** `exercise01_absolute_values`, `exercise01_converse`.

<a id="r03e02"></a>
### 3.2 — A square-root difference
**Lean source:** [Exercise02.lean](../../Math/Rudin/Chapter03/Exercise02.lean).
**Inventory status:** Verified as stated.

**Statement.** As positive integers $n$ tend to infinity,

$$
\sqrt{n^2+n}-n\longrightarrow\frac12.
$$

**Proof.** For $x>0$, rationalization gives

$$
\sqrt{x^2+x}-x=\frac{x}{\sqrt{x^2+x}+x}
=\frac1{\sqrt{1+1/x}+1}.
$$

With $x=n$, the denominator tends to $2$, which is nonzero. The quotient therefore tends to $1/2$. The value at index zero does not affect this limit.

**Lean declarations:** `exercise02_limit`.

<a id="r03e03"></a>
### 3.3 — Convergence of nested radicals
**Lean source:** [Exercise03.lean](../../Math/Rudin/Chapter03/Exercise03.lean).
**Inventory status:** Verified as stated.

**Statement.** Define $s_1=\sqrt2$ and

$$
s_{n+1}=\sqrt{2+\sqrt{s_n}}\qquad(n\geq1).
$$

Then $0\leq s_n<2$ for every $n$, and $(s_n)$ converges.

**Proof.** The initial bound holds because $0\leq\sqrt2<2$. If $0\leq s_n<2$, then $\sqrt{s_n}<2$, so $0\leq s_{n+1}<\sqrt4=2$. This proves the bound by induction. Also $s_2\geq s_1$, and the update $t\mapsto\sqrt{2+\sqrt t}$ is increasing for $t\geq0$. Induction therefore gives $s_{n+1}\geq s_n$ for all $n$. A bounded increasing real sequence converges.

**Scope.** The inner square root is part of the source recurrence; the update is not $\sqrt{2+s_n}$. Lean uses index zero for $s_1$.

**Lean declarations:** `exercise03_convergence`, `exercise03_strict_bound`.

<a id="r03e04"></a>
### 3.4 — Upper and lower limits of a parity recurrence
**Lean source:** [Exercise04.lean](../../Math/Rudin/Chapter03/Exercise04.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $s_1=0$ and, for $m\geq1$, let

$$
s_{2m}=\frac{s_{2m-1}}2,\qquad s_{2m+1}=\frac12+s_{2m}.
$$

Then $\limsup s_n=1$ and $\liminf s_n=1/2$.

**Proof.** Induction using the two recurrence rules gives, for $m\geq0$,

$$
s_{2m+1}=1-2^{-m},\qquad s_{2m+2}=\frac{1-2^{-m}}2.
$$

Consequently the odd terms tend to $1$ and the even terms tend to $1/2$. Every term is between $0$ and $1$. Moreover, both parity formulas are eventually at least $1/2-\varepsilon$, for each $\varepsilon>0$. Thus the upper limit is at most $1$ and the lower limit is at least $1/2$. The two subsequence limits give the reverse inequalities.

**Lean declarations:** `exercise04_limsup`, `exercise04_liminf`.

<a id="r03e05"></a>
### 3.5 — Upper limit of a sum
**Lean source:** [Exercise05.lean](../../Math/Rudin/Chapter03/Exercise05.lean).
**Inventory status:** Verified as stated.

**Statement.** For real sequences $(a_n)$ and $(b_n)$, put $A=\limsup a_n$ and $B=\limsup b_n$ in the extended real line. If neither $(A,B)=(-\infty,+\infty)$ nor $(A,B)=(+\infty,-\infty)$, then

$$
\limsup(a_n+b_n)\leq A+B.
$$

**Proof.** If $A,B$ are finite, then eventually $a_n\leq A+\varepsilon$ and $b_n\leq B+\varepsilon$. Hence the upper limit of the sum is at most $A+B+2\varepsilon$; let $\varepsilon\downarrow0$. If an upper limit is $+\infty$, the exclusions make the right side $+\infty$, so the inequality is automatic. The remaining infinite case has one upper limit $-\infty$ and the other finite or $-\infty$. The latter sequence is eventually bounded above by a fixed real number, while the former is eventually below any chosen real number. Their sum tends to $-\infty$. This is the extended-real upper-limit inequality used in Lean.

**Lean declarations:** `exercise05_limsup_sum`.

<a id="r03e06"></a>
### 3.6 — Four series and the complex parameter domain
**Lean source:** [Exercise06.lean](../../Math/Rudin/Chapter03/Exercise06.lean).
**Inventory status:** Verified as stated.

**Statement.** All series below start at $n=1$.

1. $\sum(\sqrt{n+1}-\sqrt n)$ diverges to $+\infty$.
2. $\sum(\sqrt{n+1}-\sqrt n)/n$ converges absolutely.
3. $\sum(n^{1/n}-1)^n$ converges absolutely.
4. For $z\in\mathbb C$, $\sum1/(1+z^n)$ is defined precisely when $z^n\ne-1$ for every positive integer $n$. The excluded parameters are exactly roots of unity of even order. On the defined domain, the series converges if and only if $|z|>1$, and in that case it converges absolutely. It diverges for defined parameters with $|z|\leq1$.

**Proof.** In (1), the first $N$ terms sum to $\sqrt{N+1}-1$, which tends to $+\infty$.

For (2), rationalization gives

$$
0\leq\frac{\sqrt{n+1}-\sqrt n}{n}
=\frac1{n(\sqrt{n+1}+\sqrt n)}\leq\frac1{n^{3/2}}.
$$

The comparison series converges.

For (3), the standard limit $n^{1/n}\to1$ implies that eventually $|n^{1/n}-1|\leq1/2$. Hence the absolute value of the $n$th term is at most $2^{-n}$.

For (4), a denominator vanishes exactly when $z^n=-1$. Such a parameter satisfies $z^{2n}=1$ and $z^n\ne1$. Conversely, these two conditions imply $(z^n-1)(z^n+1)=0$ and therefore $z^n=-1$. Equivalently, its order as a root of unity is even: an even order gives $-1$ at its half-period, while an odd order cannot admit a power equal to $-1$.

If $|z|>1$, no power can equal $-1$, since $|z^n|>1$. Eventually $|z|^n\geq2$, and

$$
|1+z^n|\geq |z|^n-1\geq\tfrac12|z|^n,
\qquad \left|\frac1{1+z^n}\right|\leq2|z|^{-n}.
$$

Geometric comparison proves absolute convergence. If $|z|<1$, the terms tend to $1$, not zero. If $|z|=1$ and the denominators are nonzero, then $|1+z^n|\leq2$, so every term has modulus at least $1/2$. In both cases ordinary convergence fails by the term test. In fact, the same lower bound applies to all defined parameters with $|z|\leq1$.

**Scope.** A parameter with a zero denominator makes the source expression undefined; it is not classified as a divergent series. No value is assigned to division by zero.

**Lean declarations:** `exercise06_a`, `exercise06_b`, `exercise06_c`, `exercise06_d_defined_parameters`, `exercise06_d_undefined_even`, `exercise06_d_convergence`, `exercise06_d_absolute`.

<a id="r03e07"></a>
### 3.7 — A weighted square-root series
**Lean source:** [Exercise07.lean](../../Math/Rudin/Chapter03/Exercise07.lean).
**Inventory status:** Verified as stated.

**Statement.** If $a_n\geq0$ for $n\geq1$ and $\sum a_n$ converges, then $\sum\sqrt{a_n}/n$ converges.

**Proof.** The inequality $(\sqrt{a_n}-1/n)^2\geq0$ gives

$$
0\leq\frac{\sqrt{a_n}}n\leq\frac12\left(a_n+\frac1{n^2}\right).
$$

The right-hand series converges. Comparison proves convergence of the nonnegative series in the statement. The hypothesis requires only convergence of the ordinary partial sums; nonnegativity justifies the summability comparison.

**Lean declarations:** `exercise07_weighted_roots`.

<a id="r03e08"></a>
### 3.8 — A bounded monotone multiplier
**Lean source:** [Exercise08.lean](../../Math/Rudin/Chapter03/Exercise08.lean).
**Inventory status:** Verified as stated.

**Statement.** Suppose $\sum a_n$ is a convergent complex series and $(b_n)$ is a bounded real sequence that is either nondecreasing or nonincreasing. Then $\sum a_nb_n$ converges. Absolute convergence of $\sum a_n$ is not required.

**Proof.** Bounded monotonicity gives a finite limit $b_n\to\ell$. The partial sums of $\sum a_n$ are bounded. The sequence $c_n=b_n-\ell$ is monotone and tends to zero. Dirichlet's test, obtained by summation by parts, gives convergence of $\sum c_na_n$; if $c_n$ is nondecreasing, apply the usual decreasing version to $-c_n$. Finally,

$$
\sum_{n<N}a_nb_n=\sum_{n<N}c_na_n+\ell\sum_{n<N}a_n,
$$

and both terms on the right converge. This is Abel's convergence test for ordinary, possibly conditional, series.

**Lean declarations:** `exercise08_monotone_multiplier`.

<a id="r03e09"></a>
### 3.9 — Four radii of convergence
**Lean source:** [Exercise09.lean](../../Math/Rudin/Chapter03/Exercise09.lean).
**Inventory status:** Verified as stated.

**Statement.** The complex power series

$$
\sum_{n\geq0}n^3z^n,\qquad
\sum_{n\geq0}\frac{2^n}{n!}z^n,\qquad
\sum_{n\geq1}\frac{2^n}{n^2}z^n,\qquad
\sum_{n\geq0}\frac{n^3}{3^n}z^n
$$

have radii of convergence $1$, $+\infty$, $1/2$, and $3$, respectively.

**Proof.** The ratios of consecutive nonzero coefficients tend, respectively, to

$$
\left(\frac{n+1}{n}\right)^3\to1,\qquad
\frac2{n+1}\to0,\qquad
2\left(\frac n{n+1}\right)^2\to2,\qquad
\frac13\left(\frac{n+1}{n}\right)^3\to\frac13.
$$

The coefficient ratio theorem gives the reciprocal of each positive limit as the radius, and infinite radius when the limit is zero. Finite initial coefficients do not affect the radius; the third series is extended by a zero constant coefficient in Lean. No boundary convergence classification is needed for these radius claims.

**Lean declarations:** `exercise09_a`, `exercise09_b`, `exercise09_c`, `exercise09_d`.

<a id="r03e10"></a>
### 3.10 — Integer coefficients restrict the radius
**Lean source:** [Exercise10.lean](../../Math/Rudin/Chapter03/Exercise10.lean).
**Inventory status:** Verified as stated.

**Statement.** If a complex power series $\sum a_nz^n$ has integer coefficients and infinitely many nonzero coefficients, its radius of convergence $R$ satisfies $R\leq1$.

**Proof.** If $R>1$, the series converges absolutely at $z=1$. In particular, $|a_n|\to0$. Eventually $|a_n|<1$, but an integer of absolute value less than $1$ is zero. This would leave only finitely many nonzero coefficients, a contradiction.

**Lean declarations:** `exercise10_integer_radius`.

<a id="r03e11"></a>
### 3.11 — Transformations of a positive divergent series
**Lean source:** [Exercise11.lean](../../Math/Rudin/Chapter03/Exercise11.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $a_n>0$ for $n\geq1$, suppose $\sum a_n$ diverges, and put $s_n=\sum_{j=1}^n a_j$, with $s_0=0$.

1. $\sum a_n/(1+a_n)$ diverges.
2. For positive integers $N,k$,

   $$
   \sum_{j=1}^k\frac{a_{N+j}}{s_{N+j}}\geq1-\frac{s_N}{s_{N+k}}.
   $$

   Consequently $\sum a_n/s_n$ diverges.
3. For $n\geq2$,

   $$
   \frac{a_n}{s_n^2}\leq\frac1{s_{n-1}}-\frac1{s_n}.
   $$

   The series $\sum_{n\geq1}a_n/s_n^2$ converges.
4. The assumptions do not decide convergence of $\sum a_n/(1+na_n)$: both convergence and divergence occur. In contrast, $\sum a_n/(1+n^2a_n)$ always converges.

**Proof.** For (1), suppose the transformed series converges. Its terms tend to zero, so eventually $a_n/(1+a_n)\leq1/2$, which implies $a_n\leq1$. On this tail,

$$
a_n\leq2\frac{a_n}{1+a_n}.
$$

Comparison would make $\sum a_n$ converge, a contradiction.

For (2), $s_{N+j}\leq s_{N+k}$, and therefore

$$
\sum_{j=1}^k\frac{a_{N+j}}{s_{N+j}}
\geq\frac{s_{N+k}-s_N}{s_{N+k}}.
$$

Since the original terms are positive and their sum diverges, $s_n\to+\infty$. For each fixed $N$, the right side tends to $1$ as $k\to\infty$. Thus tails of the transformed series cannot be arbitrarily small, contrary to the Cauchy criterion for convergence.

For (3), all denominators below are positive when $n\geq2$, and

$$
\frac1{s_{n-1}}-\frac1{s_n}
=\frac{a_n}{s_{n-1}s_n}\geq\frac{a_n}{s_n^2}.
$$

The comparison telescopes. Its partial sums from $2$ to $N$ are at most $1/s_1$. Adding the finite first term $a_1/s_1^2=1/a_1$ proves convergence. This part in fact requires only positivity, not divergence of the original series.

For the divergent example in (4), take $a_n=1$. The original series diverges and the linear transform is $\sum1/(n+1)$, which also diverges. For a convergent example, take

$$
a_n=\frac1{(n+1)^2}+\mathbf1_{\{2^j:j\geq0\}}(n).
$$

These terms are strictly positive and are at least $1$ at every power of two, so their series diverges. Away from powers of two, the linear transform is at most $(n+1)^{-2}$; at $n=2^j$ it is at most $1/n=2^{-j}$. Both comparison sums converge. Finally, for every positive sequence,

$$
0<\frac{a_n}{1+n^2a_n}\leq\frac1{n^2},
$$

which proves the quadratic-denominator assertion without a divergence hypothesis.

**Scope.** The reciprocal inequality in (3) is not asserted at $n=1$, where $s_0=0$.

**Lean declarations:** `exercise11_a`, `exercise11_b_inequality`, `exercise11_b_divergence`, `exercise11_c_inequality`, `exercise11_c_convergence`, `exercise11_d_linear_classification`, `exercise11_d_linear_convergent_example`, `exercise11_d_linear_divergent_example`, `exercise11_d_quadratic`.

<a id="r03e12"></a>
### 3.12 — Transformations using positive tails
**Lean source:** [Exercise12.lean](../../Math/Rudin/Chapter03/Exercise12.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $a_n>0$ for $n\geq1$, suppose $\sum a_n$ converges, and set $r_n=\sum_{j=n}^{\infty}a_j$.

1. For positive integers $m<n$,

   $$
   \sum_{j=m}^n\frac{a_j}{r_j}>1-\frac{r_n}{r_m}.
   $$

   The series $\sum a_n/r_n$ diverges.
2. For every $n\geq1$,

   $$
   \frac{a_n}{\sqrt{r_n}}<2(\sqrt{r_n}-\sqrt{r_{n+1}}).
   $$

   The series $\sum a_n/\sqrt{r_n}$ converges.

**Proof.** The tails satisfy $r_n>r_{n+1}>0$, $r_n-r_{n+1}=a_n$, and $r_n\to0$. For (1), use $r_j\leq r_m$ when $j\geq m$:

$$
\sum_{j=m}^n\frac{a_j}{r_j}
\geq\frac{r_m-r_{n+1}}{r_m}
>\frac{r_m-r_n}{r_m}.
$$

For each fixed $m$, the last expression tends to $1$ as $n\to\infty$. A convergent transformed series would therefore have every infinite tail at least $1$, whereas its tails must tend to zero. This contradiction proves divergence.

For (2), put $x=\sqrt{r_n}$ and $y=\sqrt{r_{n+1}}$. Then $0<y<x$ and

$$
\frac{a_n}{\sqrt{r_n}}=\frac{x^2-y^2}{x}
=(x-y)\left(1+\frac yx\right)<2(x-y).
$$

Summing this bound telescopes and bounds all partial sums by $2\sqrt{r_1}$. Since the terms are positive, the series converges.

**Lean declarations:** `exercise12_a_inequality`, `exercise12_a_divergence`, `exercise12_b_inequality`, `exercise12_b_convergence`.

<a id="r03e13"></a>
### 3.13 — Absolute convergence of a Cauchy product
**Lean source:** [Exercise13.lean](../../Math/Rudin/Chapter03/Exercise13.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $\sum_{n\geq0}a_n$ and $\sum_{n\geq0}b_n$ be absolutely convergent complex series. Their Cauchy product, with coefficients

$$
c_n=\sum_{k=0}^n a_kb_{n-k},
$$

is absolutely convergent.

**Proof.** Write $A=\sum|a_n|$ and $B=\sum|b_n|$. The triangle inequality and nonnegativity give, for each $N$,

$$
\sum_{n=0}^N|c_n|
\leq\sum_{\substack{k,j\geq0\\k+j\leq N}}|a_k||b_j|
\leq AB.
$$

Thus the increasing partial sums of $\sum|c_n|$ are bounded and converge. This is the standard absolute Cauchy-product theorem used in Lean. Both hypotheses refer to ordered partial sums of absolute values, not to an assumed unconditional interpretation of a conditionally convergent series.

**Lean declarations:** `exercise13_absolute_cauchy_product`.

<a id="r03e14"></a>
### 3.14 — Arithmetic means and Tauberian converses
**Lean source:** [Exercise14.lean](../../Math/Rudin/Chapter03/Exercise14.lean).
**Inventory status:** Verified refutation and correction.

**Statement.** For a complex sequence $(s_n)_{n\geq0}$ define

$$
\sigma_n=\frac1{n+1}\sum_{k=0}^n s_k,\qquad a_n=s_n-s_{n-1}\quad(n\geq1).
$$

1. If $s_n\to s$, then $\sigma_n\to s$.
2. The converse fails: a nonconvergent sequence can have $\sigma_n\to0$.
3. This can occur even with every $s_n$ a positive real number and $\limsup s_n=+\infty$.
4. For $n\geq1$,

   $$
   s_n-\sigma_n=\frac1{n+1}\sum_{k=1}^n k a_k.
   $$

   If $na_n\to0$ and $\sigma_n\to\sigma$, then $s_n\to\sigma$.
5. The same conclusion holds under the weaker hypothesis that there is a finite real $M$ with $|ka_k|\leq M$ for every $k\geq1$. For $0\leq m<n$ the prescribed identity is

   $$
   s_n-\sigma_n=\frac{m+1}{n-m}(\sigma_n-\sigma_m)
      +\frac1{n-m}\sum_{i=m+1}^n(s_n-s_i).
   $$

   For $m<i\leq n$, the bounds used in the proof are

   $$
   |s_n-s_i|\leq\frac{(n-i)M}{i+1}\leq\frac{(n-m-1)M}{m+2}.
   $$

   With the floor choice specified below, the corrected final bound is $|s_n-s_i|\leq M\varepsilon$. It is strict if $M>0$.

**Correction.** The source prints $|s_n-s_i|<M\varepsilon$ while allowing $M=0$. The zero sequence satisfies all bound and mean-convergence assumptions with $M=0$, but the strict bound would be $0<0$. This refutes only that intermediate strict estimate. The non-strict correction proves the unchanged final converse without strengthening its hypotheses.

**Proof.** For (1), fix $\varepsilon>0$ and choose $K$ such that $|s_k-s|<\varepsilon$ for $k\geq K$. For $n\geq K$,

$$
|\sigma_n-s|\leq\frac1{n+1}\sum_{k<K}|s_k-s|+\varepsilon.
$$

The finite first sum divided by $n+1$ tends to zero, proving the arithmetic-mean theorem.

For (2) and (3), use the construction proved in the source file. Put

$$
F(n)=\lfloor n^{1/4}\rfloor^2,\qquad
s_n=F(n)-F(n-1)+\frac1{n+1},
$$

where $F(-1)$ is interpreted as $F(0)=0$ for the term at $n=0$. The function $F$ is nondecreasing, so $s_n>0$. At $n=(k+1)^4$, the jump in $F$ is $2k+1$, so $s_{(k+1)^4}\geq2k+1$ and $\limsup s_n=+\infty$. On the other hand, telescoping yields

$$
\sigma_n=\frac{F(n)}{n+1}+\frac1{n+1}\sum_{k=0}^n\frac1{k+1}.
$$

The first term tends to zero since $F(n)\leq\sqrt n$. The second tends to zero by (1), applied to $1/(k+1)$. This positive real sequence, also regarded as complex, proves both assertions and cannot have a finite limit.

For (4), expand and telescope the weighted differences:

$$
\sum_{k=1}^n k(s_k-s_{k-1})=(n+1)s_n-\sum_{k=0}^n s_k.
$$

This is the claimed identity. When $ka_k\to0$, its arithmetic means tend to zero by (1), and hence $s_n-\sigma_n\to0$.

For (5), subtract the two identities defining $(n+1)\sigma_n$ and $(m+1)\sigma_m$, and expand the sum of $s_n-s_i$. Rearrangement gives the stated block identity. The bound on $|ka_k|$ implies $M\geq0$. Since

$$
s_n-s_i=\sum_{k=i+1}^n a_k,\qquad |a_k|\leq\frac Mk\leq\frac M{i+1},
$$

the first estimate follows by the triangle inequality. The second follows from $i\geq m+1$, which bounds the numerator above by $(n-m-1)M$ and the denominator below by $m+2$.

Fix $\varepsilon>0$. For $n\geq\varepsilon$, choose

$$
m=\left\lfloor\frac{n-\varepsilon}{1+\varepsilon}\right\rfloor.
$$

The floor inequalities give

$$
0\leq m<n,\qquad
m\leq\frac{n-\varepsilon}{1+\varepsilon}<m+1,\qquad
\frac{m+1}{n-m}\leq\frac1\varepsilon,\qquad
\frac{n-m-1}{m+2}<\varepsilon.
$$

Indeed, the lower floor bound gives $\varepsilon(m+1)\leq n-m$, and the upper bound gives $n-m-1<\varepsilon(m+2)$. Thus $|s_n-s_i|\leq M\varepsilon$ for $m<i\leq n$, with strict inequality when $M>0$. For $M=0$, the zero-sequence obstruction applies at every $n\geq1$ with $\varepsilon=1$ and this same floor index; in particular $i=n$ is permitted.

Taking norms in the block identity and using its $n-m$ summands gives

$$
|s_n-\sigma|\leq\frac1\varepsilon|\sigma_n-\sigma_m|
+M\varepsilon+|\sigma_n-\sigma|.
$$

For fixed $\varepsilon$, this choice of $m$ tends to infinity with $n$. If $\sigma_n\to\sigma$, the right side tends to $M\varepsilon$. Therefore, in the extended real sense,

$$
\limsup_{n\to\infty}|s_n-\sigma|\leq M\varepsilon
$$

for every $\varepsilon>0$. Letting $\varepsilon\downarrow0$ and using nonnegativity proves $s_n\to\sigma$, including the case $M=0$.

**Lean declarations:** `exercise14_a`, `exercise14_b`, `exercise14_c`, `exercise14_d_identity`, `exercise14_d_convergence`, `exercise14_e_identity`, `exercise14_e_estimate`, `exercise14_e_index_choice`, `exercise14_e_index_estimate`, `exercise14_e_limsup`, `exercise14_e_convergence`, `exercise14_e_zero_bound_obstruction`, `exercise14_e_index_estimate_strict`.

<a id="r03e15"></a>
### 3.15 — Series in Euclidean space
**Lean source:** [Exercise15.lean](../../Math/Rudin/Chapter03/Exercise15.lean).
**Inventory status:** Verified as stated.

**Statement.** Fix a positive integer $k$ and use the Euclidean norm on $\mathbb R^k$. Series convergence means convergence of the ordered partial sums $S_N=\sum_{n=0}^{N-1}a_n$. The following extensions of the scalar series theorems hold.

1. **Cauchy criterion (3.22).** The series converges if and only if for every $\varepsilon>0$ there is $N$ such that

   $$
   \left\|\sum_{j=n}^m a_j\right\|\leq\varepsilon\qquad(m\geq n\geq N).
   $$

2. **Term test (3.23).** Convergence implies $a_n\to0$.
3. **Comparison (3.25(a)).** If a real series $\sum c_n$ converges and $\|a_n\|\leq c_n$ eventually, then $\sum a_n$ converges.
4. **Root test (3.33).** Put $L=\limsup_{n\to\infty}\|a_n\|^{1/n}$, using $n\geq1$ and extended nonnegative values. If $L<1$, the series converges; if $L>1$, it diverges. The case $L=1$ does not decide convergence.
5. **Ratio test (3.34).** Assume $a_n\ne0$ eventually, so the norm ratios are defined on a tail. If $\limsup\|a_{n+1}\|/\|a_n\|<1$, the series converges. If these ratios are at least $1$ eventually, it diverges.
6. **Dirichlet test (3.42).** If $(S_N)$ is bounded and the real sequence $b_n$ is nonincreasing with limit zero, then $\sum b_na_n$ converges.
7. **Absolute convergence (3.45).** If $\sum\|a_n\|$ converges, then $\sum a_n$ converges.
8. **Linearity (3.47).** If $\sum a_n=A$ and $\sum b_n=B$, then $\sum(a_n+b_n)=A+B$. For each fixed real $c$, $\sum ca_n=cA$.
9. **Rearrangements (3.55).** Every rearrangement by a permutation of the natural numbers of an absolutely convergent vector series converges to the original sum.

**Proof.** For (1), an inclusive tail is $S_{m+1}-S_n$. Thus convergence implies the displayed condition. Conversely, apply the condition with tolerance $\varepsilon/2$ to see that the partial sums form a Cauchy sequence. Completeness of $\mathbb R^k$ gives a limit. For (2), $a_n=S_{n+1}-S_n\to0$.

For (3), discard the finite initial segment on which the comparison need not hold. On the remaining tail $c_n\geq0$, and

$$
\left\|\sum_{j=n}^m a_j\right\|\leq\sum_{j=n}^m\|a_j\|\leq\sum_{j=n}^m c_j.
$$

The scalar Cauchy criterion and (1) give convergence. Taking $c_n=\|a_n\|$ also proves (7).

For (4), if $L<1$, choose $q$ with $L<q<1$. Eventually $\|a_n\|^{1/n}\leq q$, so $\|a_n\|\leq q^n$ and geometric comparison applies. If a series converges, then eventually $\|a_n\|<1$, so its upper root limit is at most $1$. This proves divergence when $L>1$, including $L=+\infty$. For the boundary case choose a unit vector $v$: the series with $a_0=0$ and $a_n=n^{-2}v$ for $n\geq1$ converges, while the constant terms $b_n=v$ give a divergent series. Both upper root limits equal $1$, since $n^{-2/n}\to1$.

For (5), choose a number $q<1$ above the upper ratio limit. The eventual estimate $\|a_{n+1}\|\leq q\|a_n\|$ gives a geometric bound by induction. In the divergence case, the norms on a sufficiently late tail are nondecreasing and bounded below by a positive initial norm. They cannot tend to zero.

For (6), write $a_n=S_{n+1}-S_n$ and use summation by parts. If $\|S_j\|\leq M$, then for $m\geq n$,

$$
\sum_{j=n}^m b_ja_j
=b_mS_{m+1}-b_nS_n+\sum_{j=n+1}^m(b_{j-1}-b_j)S_j.
$$

Since a nonincreasing sequence tending to zero is nonnegative, the norm of this tail is at most $2Mb_n$, which tends to zero. The Cauchy criterion applies.

For (8), finite sums distribute over addition and scalar multiplication; continuity of these operations gives the asserted limits. For (9), choose a finite initial set outside which the sum of norms is small. Every sufficiently long rearranged partial sum contains that set, and its difference from the full sum is bounded by the remaining sum of norms. Thus its limit is unchanged.

**Scope.** No absolute-convergence assumption is added to the Cauchy criterion, term test, Dirichlet test, or linearity statements. Ratios are ratios of norms, not vector quotients, and zero denominators are excluded eventually. The file also handles $k=0$: every term is the zero vector, every series converges, and the upper root limit is $0$. The root-test boundary examples require $k>0$.

**Lean declarations:** `exercise15_cauchy_criterion`, `exercise15_terms_tend_zero`, `exercise15_comparison`, `exercise15_root_convergence`, `exercise15_root_divergence`, `exercise15_root_boundary`, `exercise15_dimension_zero`, `exercise15_ratio_convergence`, `exercise15_ratio_divergence`, `exercise15_dirichlet`, `exercise15_absolute_implies_convergent`, `exercise15_addition`, `exercise15_scalar_multiplication`, `exercise15_rearrangements`.

<a id="r03e16"></a>
### 3.16 — Newton iteration for a square root
**Lean source:** [Exercise16.lean](../../Math/Rudin/Chapter03/Exercise16.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $\alpha>0$, let $x_1>\sqrt\alpha$, and define

$$
x_{n+1}=\frac12\left(x_n+\frac\alpha{x_n}\right).
$$

Then $x_n>\sqrt\alpha$ for all $n$, the sequence is strictly decreasing, and $x_n\to\sqrt\alpha$. For $\varepsilon_n=x_n-\sqrt\alpha$ and $\beta=2\sqrt\alpha$,

$$
\varepsilon_{n+1}=\frac{\varepsilon_n^2}{2x_n}
<\frac{\varepsilon_n^2}{\beta},\qquad
\varepsilon_{n+1}<\beta\left(\frac{\varepsilon_1}{\beta}\right)^{2^n}\quad(n\geq1).
$$

When $\alpha=3$ and $x_1=2$,

$$
\frac{\varepsilon_1}{\beta}<\frac1{10},\qquad
\varepsilon_5<4\cdot10^{-16},\qquad
\varepsilon_6<4\cdot10^{-32}.
$$

**Proof.** Put $r=\sqrt\alpha>0$. For $x>r$, direct algebra gives

$$
\frac{x+\alpha/x}{2}-r=\frac{(x-r)^2}{2x}>0.
$$

Also $\alpha/x<x$, so the update is strictly less than $x$. Induction proves positivity of all denominators, the strict lower bound, and strict decrease. Thus $x_n\to L\geq r>0$. Passing to the limit in the recurrence gives $L=(L+\alpha/L)/2$, hence $L^2=\alpha$ and $L=r$.

The displayed algebra is the exact error identity. Since $x_n>r$ and $\varepsilon_n>0$, replacing $2x_n$ by $\beta$ makes the quotient strictly larger. Dividing by $\beta$ gives $\varepsilon_{n+1}/\beta<(\varepsilon_n/\beta)^2$; induction gives the iterated error estimate. No assumption that $\varepsilon_1/\beta<1$ is needed for that inequality or for convergence already proved.

For the numerical case, $\sqrt3>5/3$ implies

$$
\frac{2-\sqrt3}{2\sqrt3}<\frac1{10},
$$

and $2\sqrt3<4$. Apply the general estimate with $n=4$ and $n=5$ to obtain the fifth- and sixth-term bounds.

**Lean declarations:** `exercise16_monotone`, `exercise16_limit`, `exercise16_error_step`, `exercise16_error_bound`, `exercise16_initial_bound`, `exercise16_fifth_bound`, `exercise16_sixth_bound`.

<a id="r03e17"></a>
### 3.17 — Alternating square-root iteration and its rate
**Lean source:** [Exercise17.lean](../../Math/Rudin/Chapter03/Exercise17.lean).
**Inventory status:** Verified as stated.

**Statement.** Suppose $\alpha>1$ and $x_1>\sqrt\alpha$. Define

$$
x_{n+1}=\frac{\alpha+x_n}{1+x_n}
=x_n+\frac{\alpha-x_n^2}{1+x_n}.
$$

Then

$$
x_1>x_3>x_5>\cdots>\sqrt\alpha,\qquad
x_2<x_4<x_6<\cdots<\sqrt\alpha,
$$

and the full sequence tends to $\sqrt\alpha$. Writing $r=\sqrt\alpha$, its successive-error ratios satisfy

$$
\frac{x_{n+1}-r}{x_n-r}\longrightarrow\frac{1-r}{1+r},\qquad
\frac{|x_{n+1}-r|}{|x_n-r|}\longrightarrow\frac{r-1}{r+1}\in(0,1).
$$

Thus convergence is linear. For the Newton sequence $(y_n)$ of Exercise 3.16, under its hypotheses $\alpha>0$ and $y_1>r$,

$$
\frac{y_{n+1}-r}{y_n-r}\to0,\qquad
\frac{y_{n+1}-r}{(y_n-r)^2}\to\frac1{2r},
$$

so that method has quadratic convergence.

**Proof.** All iterates are positive. With $f(y)=(\alpha+y)/(1+y)$,

$$
f(y)-r=\frac{(1-r)(y-r)}{1+y}.
$$

Since $r>1$, each step changes the sign of the nonzero error. Moreover,

$$
f(f(y))-y=\frac{2(\alpha-y^2)}{\alpha+1+2y}.
$$

The denominator is positive. This difference is negative above $r$ and positive below $r$, proving the strict odd and even monotonicity.

For convergence, define $t_n=(x_n-r)/(x_n+r)$. Algebra gives

$$
t_n=\left(\frac{1-r}{1+r}\right)^{n-1}\frac{x_1-r}{x_1+r}.
$$

The multiplier has absolute value less than $1$, so $t_n\to0$. Since $x_n=r(1+t_n)/(1-t_n)$, it follows that $x_n\to r$. Dividing the error identity by $x_n-r\ne0$ gives the signed ratio $(1-r)/(1+x_n)$ and therefore its stated limit; taking absolute values gives the positive rate.

For Newton's method, the exact error identity from Exercise 3.16 gives the two ratios

$$
\frac{y_n-r}{2y_n},\qquad\frac1{2y_n}.
$$

Because $y_n\to r>0$, their limits are $0$ and $1/(2r)$, respectively.

**Lean declarations:** `exercise17_odd_decreasing`, `exercise17_even_increasing`, `exercise17_limit`, `exercise17_rate`, `exercise17_absolute_rate`, `exercise17_newton_comparison`, `exercise17_newton_quadratic_rate`.

<a id="r03e18"></a>
### 3.18 — Newton iteration for positive integer roots
**Lean source:** [Exercise18.lean](../../Math/Rudin/Chapter03/Exercise18.lean).
**Inventory status:** Verified as stated.

**Statement.** Retain $\alpha>0$ and $x_1>\sqrt\alpha$ from Exercise 3.16. For a positive integer $p$, replace its update by

$$
x_{n+1}=N(x_n),\qquad
N(x)=\frac{p-1}{p}x+\frac\alpha p x^{1-p}
=\frac{(p-1)x+\alpha/x^{p-1}}p.
$$

Every iterate is positive, and all powers and denominators in this real formula are defined.

1. If $p=1$, then $x_n=\alpha$ for every $n\geq2$; the limit is reached after one update.
2. If $p\geq2$, let $r=\alpha^{1/p}$ be the unique positive root of $r^p=\alpha$. Then $x_n\to r$, with three cases:
   - If $x_1<r$, the first step increases past $r$: $x_1<r<x_2$. From $x_2$ onward the sequence is strictly decreasing and stays above $r$.
   - If $x_1=r$, every term equals $r$.
   - If $x_1>r$, the entire sequence is strictly decreasing and stays above $r$.

**Proof.** The inherited initial bound implies $x_1>0$. For $p\geq1$ and $x>0$, the numerator of $N(x)$ is positive: $(p-1)x\geq0$ and $\alpha/x^{p-1}>0$. Thus positivity follows by induction, $p\ne0$, and $x_n^{p-1}\ne0$. On this domain the integer power $x^{1-p}$ is exactly the reciprocal of $x^{p-1}$. For $p=1$, the formula reduces to $N(x)=\alpha$.

Now suppose $p\geq2$. The positive real power $r=\alpha^{1/p}$ has $r^p=\alpha$, and strict monotonicity of $t\mapsto t^p$ on positive reals gives uniqueness. Direct algebra yields

$$
N(x)-x=\frac{r^p-x^p}{p x^{p-1}}.
$$

Also $N(r)=r$. For $x>0$ with $x\ne r$, the strict Bernoulli inequality applied to $r/x>0$ gives

$$
\left(\frac rx\right)^p>1+p\left(\frac rx-1\right),
$$

so

$$
N(x)-r=\frac xp\left[\left(\frac rx\right)^p-1-p\left(\frac rx-1\right)\right]>0.
$$

Thus every non-root positive start maps strictly above $r$. The difference formula then proves all the stated directions of motion and the constant case.

For $x\geq r$, one has $r^p/x^{p-1}\leq r$, and hence

$$
0\leq N(x)-r\leq\frac{p-1}{p}(x-r).
$$

The factor lies in $[0,1)$. Iteration bounds the errors by a geometric sequence and proves convergence for a start above $r$. A start below $r$ is covered after its first step. This bound proves convergence but does not assert an exact asymptotic order.

**Scope.** The starting hypothesis is not silently replaced by $x_1>\alpha^{1/p}$. The classification is proved for every positive start and then specialized to the inherited bound. That bound really allows the below-root case: for $\alpha=1/64$, $p=3$, and $x_1=3/16$,

$$
\sqrt\alpha=\frac18<\frac3{16}<\frac14=r<x_2.
$$

The formula concerns the positive real branch only; $p=0$, nonpositive starts, and other real or complex roots are outside the stated domain.

**Lean declarations:** `exercise18_well_defined`, `exercise18_source_update`, `exercise18_unit_exponent`, `exercise18_unit_limit`, `exercise18_higher_exponents`, `exercise18_below_example`.

<a id="r03e19"></a>
### 3.19 — Ternary series and the Cantor set
**Lean source:** [Exercise19.lean](../../Math/Rudin/Chapter03/Exercise19.lean).
**Inventory status:** Verified as stated.

**Statement.** The middle-thirds Cantor set is exactly

$$
\left\{\sum_{n=1}^{\infty}\frac{\alpha_n}{3^n}:\alpha_n\in\{0,2\}\text{ for every }n\right\}.
$$

Every displayed series converges, and every Cantor-set point, including endpoints, has such a representation.

**Proof.** The terms are nonnegative and at most $2/3^n$, so geometric comparison proves convergence. For a prescribed sequence of digits let $t_m=\sum_{n=1}^m\alpha_n/3^n$. The remaining tail lies in $[0,3^{-m}]$. The interval $[t_m,t_m+3^{-m}]$ is one of the closed intervals retained at stage $m$ of the middle-thirds construction: a digit $0$ chooses the left third, and a digit $2$ chooses the right third. The series sum therefore lies in every stage and hence in the Cantor set.

Conversely, if $x$ belongs to the Cantor set, at each stage choose the retained third containing $x$, consistently inside the preceding chosen interval. These choices give digits $\alpha_n\in\{0,2\}$ and intervals $[t_m,t_m+3^{-m}]$ containing $x$. Thus $|x-t_m|\leq3^{-m}\to0$, proving the representation. Closed intervals retain their endpoints, so this argument includes $0$, $1$, and all deleted-interval endpoints. It does not require a unique unrestricted ternary expansion; for example $1/3=\sum_{n=2}^{\infty}2/3^n$. Lean uses the standard ternary characterization of the literal middle-thirds construction.

**Lean declarations:** `exercise19_digits_in_cantor`, `exercise19_cantor_has_digits`, `exercise19_image`.

<a id="r03e20"></a>
### 3.20 — A convergent subsequence of a Cauchy sequence
**Lean source:** [Exercise20.lean](../../Math/Rudin/Chapter03/Exercise20.lean).
**Inventory status:** Verified as stated.

**Statement.** In any metric space $X$, let $(p_n)$ be Cauchy and let $\varphi:\mathbb N\to\mathbb N$ be strictly increasing. If $p_{\varphi(j)}\to p\in X$, then $p_n\to p$. Completeness of $X$ is not assumed.

**Proof.** Given $\varepsilon>0$, choose $N$ such that $d(p_n,p_m)<\varepsilon/2$ for $m,n\geq N$. Since $\varphi(j)\to\infty$, choose $j$ with $\varphi(j)\geq N$ and $d(p_{\varphi(j)},p)<\varepsilon/2$. Then for every $n\geq N$,

$$
d(p_n,p)\leq d(p_n,p_{\varphi(j)})+d(p_{\varphi(j)},p)<\varepsilon.
$$

**Lean declarations:** `exercise20_full_convergence`.

<a id="r03e21"></a>
### 3.21 — Nested sets with vanishing diameter
**Lean source:** [Exercise21.lean](../../Math/Rudin/Chapter03/Exercise21.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $X$ be a complete metric space, and let $E_n$ be nonempty closed bounded subsets with $E_{n+1}\subseteq E_n$ and $\operatorname{diam}(E_n)\to0$. Then $\bigcap_nE_n$ consists of exactly one point. Uniqueness alone requires only boundedness of each $E_n$ and vanishing diameter, not completeness, closedness, nonemptiness, or nesting.

**Proof.** Choose $x_n\in E_n$. If $m,n\geq N$, nesting puts both points in $E_N$, so

$$
d(x_m,x_n)\leq\operatorname{diam}(E_N).
$$

Thus $(x_n)$ is Cauchy and has a limit $x\in X$. For each fixed $N$, its tail lies in the closed set $E_N$, so $x\in E_N$. This proves nonemptiness of the intersection. If $x,y$ both lie in every $E_n$, boundedness gives $d(x,y)\leq\operatorname{diam}(E_n)$ for all $n$. Passing to the limit gives $d(x,y)=0$, so $x=y$. The last argument establishes the stated weaker hypotheses for uniqueness.

**Lean declarations:** `exercise21_intersection_exists`, `exercise21_intersection_unique`, `exercise21_singleton`.

<a id="r03e22"></a>
### 3.22 — Baire's theorem
**Lean source:** [Exercise22.lean](../../Math/Rudin/Chapter03/Exercise22.lean).
**Inventory status:** Verified as stated.

**Statement.** If $X$ is a nonempty complete metric space and each $G_n$ is open and dense in $X$, then $\bigcap_nG_n$ is nonempty and dense. Density itself holds without the nonempty-space assumption.

**Proof.** This is Baire's theorem for complete metric spaces, as used in Lean. To see the nested-set argument, start with any nonempty open set $U$. Density and openness allow a nonempty closed ball $B_1$ of positive radius inside $U\cap G_1$. Inductively choose a nonempty closed ball $B_{n+1}$ inside the open ball with the same center and radius as $B_n$, intersected with $G_{n+1}$, and give it radius at most $2^{-(n+1)}$. This is possible because that intersection is nonempty and open. Choose the first radius at most $1/2$ as well. The balls are nested, closed, bounded, and have diameters tending to zero. Exercise 3.21 supplies a common point. It belongs to $U$ and every $G_n$. Thus every nonempty open set meets the intersection, proving density. If $X$ is nonempty, take $U=X$ to obtain nonemptiness. If $X$ is empty, density is vacuous but nonemptiness is not asserted.

**Lean declarations:** `exercise22_baire_nonempty`, `exercise22_baire_dense`.

<a id="r03e23"></a>
### 3.23 — Limits of distances between Cauchy sequences
**Lean source:** [Exercise23.lean](../../Math/Rudin/Chapter03/Exercise23.lean).
**Inventory status:** Verified as stated.

**Statement.** If $(p_n)$ and $(q_n)$ are Cauchy sequences in any metric space $X$, then $d(p_n,q_n)$ has a finite real limit. The space $X$ need not be complete.

**Proof.** Two applications of the triangle inequality give

$$
|d(p_n,q_n)-d(p_m,q_m)|\leq d(p_n,p_m)+d(q_n,q_m).
$$

Both terms on the right are uniformly small for sufficiently large $m,n$. Thus the real distance sequence is Cauchy, and completeness of $\mathbb R$ gives a finite limit. The Lean proof expresses the same fact through uniform continuity of the distance function.

**Lean declarations:** `exercise23_distance_limit`.

<a id="r03e24"></a>
### 3.24 — Completion by classes of Cauchy sequences
**Lean source:** [Exercise24.lean](../../Math/Rudin/Chapter03/Exercise24.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $X$ be any metric space, with no nonemptiness assumption. On its Cauchy sequences define

$$
(p_n)\sim(q_n)\quad\Longleftrightarrow\quad d(p_n,q_n)\to0.
$$

1. This is an equivalence relation.
2. On the quotient $X^*$, the formula

   $$
   \Delta([(p_n)],[(q_n)])=\lim_{n\to\infty}d(p_n,q_n)
   $$

   is well defined and is a metric.
3. The metric space $X^*$ is complete.
4. The map $\varphi:X\to X^*$ sending $p$ to the class of the constant sequence $p,p,\ldots$ is an isometric embedding:

   $$
   \Delta(\varphi(p),\varphi(q))=d(p,q).
   $$

5. Its image is dense in $X^*$. If $X$ is complete, $\varphi$ is surjective, so $\varphi(X)=X^*$.

**Proof.** Reflexivity and symmetry in (1) follow from the corresponding metric axioms. If $p\sim q$ and $q\sim r$, then

$$
0\leq d(p_n,r_n)\leq d(p_n,q_n)+d(q_n,r_n)\to0,
$$

which proves transitivity.

By Exercise 3.23, the real limit defining $\Delta$ exists for every pair of Cauchy sequences. If $p\sim p'$ and $q\sim q'$, then

$$
|d(p_n,q_n)-d(p'_n,q'_n)|\leq d(p_n,p'_n)+d(q_n,q'_n)\to0.
$$

Thus the limit is independent of both representatives. Nonnegativity, symmetry, and the triangle inequality pass to limits. Self-distance is zero, and $\Delta(P,Q)=0$ holds exactly when their representatives are equivalent, that is, exactly when $P=Q$. This proves every metric axiom in (2).

For (3), the Lean construction identifies this actual sequence quotient with the standard complete metric completion $\widehat X$; it does not replace the quotient definition. Let $\iota:X\to\widehat X$ be the standard dense isometric embedding. Every Cauchy sequence $(p_n)$ has a limit $\widehat p$ after applying $\iota$. Continuity of distance gives

$$
\lim_n d(p_n,q_n)=d(\widehat p,\widehat q).
$$

Consequently two sequences are equivalent exactly when these limits in $\widehat X$ agree. The map $[(p_n)]\mapsto\widehat p$ is therefore well defined and injective, and it preserves the metric already specified by $\Delta$. It is surjective: density of $\iota(X)$ gives, for each $z\in\widehat X$, a sequence $\iota(p_n)\to z$. The sequence $(p_n)$ is Cauchy because $\iota$ preserves distances, and its class maps to $z$. Hence the quotient is isometric to the complete space $\widehat X$ and is complete. These are the standard completion and sequential-closure results used by the Lean proof.

For (4), the distance between two constant sequences is constantly $d(p,q)$. Taking its limit proves the identity and hence injectivity.

For (5), if $P=[(p_n)]$, then $\varphi(p_n)\to P$. Indeed, given $\varepsilon>0$, Cauchyness gives $N$ such that $d(p_n,p_m)<\varepsilon/2$ for $m,n\geq N$. For fixed $n\geq N$, taking $m\to\infty$ yields $\Delta(\varphi(p_n),P)\leq\varepsilon/2<\varepsilon$. Thus every class lies in the closure of the image. If $X$ is complete, a representative $(p_n)$ converges to some $p\in X$, so it is equivalent to the constant sequence at $p$. Every class is then $\varphi(p)$.

**Scope.** If $X$ is empty, there are no sequences $\mathbb N\to X$, so $X^*$ is empty. It is still a complete metric space, the embedding has dense image, and the asserted surjectivity is valid. No arbitrary point of $X$ is assumed in the construction.

**Lean declarations:** `exercise24_a`, `sequence_distance_limit`, `exercise24_b_well_defined`, `dist_eq_delta`, `distance_limit`, `exercise24_b_metric`, `exercise24_c`, `exercise24_d_embedding`, `exercise24_d`, `embed_injective`, `exercise24_e_density`, `exercise24_e_surjective`, `exercise24_e_range`.

<a id="r03e25"></a>
### 3.25 — The completion of the rational numbers
**Lean source:** [Exercise25.lean](../../Math/Rudin/Chapter03/Exercise25.lean).
**Inventory status:** Verified as stated.

**Statement.** For the rational metric $d(p,q)=|p-q|$, the sequence-quotient completion $\mathbb Q^*$ from Exercise 3.24 is isometric to $\mathbb R$. There is an isometric bijection $T:\mathbb Q^*\to\mathbb R$ such that

$$
T(\varphi(q))=q\quad(q\in\mathbb Q),\qquad
\Delta(P,Q)=|T(P)-T(Q)|.
$$

For every rational Cauchy sequence $(q_n)$, its ordinary real limit is $T([(q_n)])$. The domain is complete and the image of the original rationals is dense in $\mathbb R$.

**Proof.** The usual inclusion $\mathbb Q\hookrightarrow\mathbb R$ preserves the stated distance. Every rational Cauchy sequence therefore has a real limit. Define $T([(q_n)])=\lim_n q_n$. Equivalent representatives have the same limit, and continuity of absolute value gives

$$
\Delta([(p_n)],[(q_n)])=\lim_n|p_n-q_n|
=|T([(p_n)])-T([(q_n)])|.
$$

Thus $T$ is an isometry and is injective. A constant rational sequence has its rational value as real limit, proving compatibility with $\varphi$ and the representative-limit assertion.

By Exercise 3.24 the domain is complete. The image of a complete space under an isometry into a metric space is closed. Here the image contains every rational number, and the rationals are dense in $\mathbb R$, so that closed image is all of $\mathbb R$. Hence $T$ is surjective and gives the required isometric identification. Its values on $\varphi(\mathbb Q)$ are precisely the ordinary rational points, whose density proves the last claim.

**Lean declarations:** `exercise25_identification`, `exercise25_distance`, `exercise25_representative_limit`, `exercise25_rational_completion_embed`, `exercise25_completeness_density`.

<a id="chapter-04"></a>

## Chapter 4 — Continuity

**Exercises:** [1](#r04e01) · [2](#r04e02) · [3](#r04e03) · [4](#r04e04) · [5](#r04e05) · [6](#r04e06) · [7](#r04e07) · [8](#r04e08) · [9](#r04e09) · [10](#r04e10) · [11](#r04e11) · [12](#r04e12) · [13](#r04e13) · [14](#r04e14) · [15](#r04e15) · [16](#r04e16) · [17](#r04e17) · [18](#r04e18) · [19](#r04e19) · [20](#r04e20) · [21](#r04e21) · [22](#r04e22) · [23](#r04e23) · [24](#r04e24) · [25](#r04e25) · [26](#r04e26)

<a id="r04e01"></a>
### 4.1 — Symmetric differences do not imply continuity
**Lean source:** [Exercise01.lean](../../Math/Rudin/Chapter04/Exercise01.lean).
**Inventory status:** Verified as stated.

**Statement.** The condition

$$
\lim_{h\to0}\bigl(f(x+h)-f(x-h)\bigr)=0\qquad(x\in\mathbb R)
$$

does not imply that $f:\mathbb R\to\mathbb R$ is continuous.

**Proof.** Set $f(0)=1$ and $f(x)=0$ for $x\ne0$. At $x=0$, the symmetric difference is zero for every $h$. At $x\ne0$, it is zero whenever $|h|<|x|$, since neither $x+h$ nor $x-h$ is zero. Thus even the unpunctured limit holds at every $x$. Nevertheless, $f(h)=0$ for every nonzero $h$, whereas $f(0)=1$, so $f$ is not continuous at zero.

**Lean declarations:** `exercise01_symmetric_difference_converse`.

<a id="r04e02"></a>
### 4.2 — Images of closures
**Lean source:** [Exercise02.lean](../../Math/Rudin/Chapter04/Exercise02.lean).
**Inventory status:** Verified as stated.

**Statement.** If $f:X\to Y$ is continuous between metric spaces and $E\subseteq X$, then

$$
f(\overline E)\subseteq\overline{f(E)}.
$$

The inclusion can be strict.

**Proof.** The closed set $f^{-1}(\overline{f(E)})$ contains $E$, so it contains $\overline E$. This proves the inclusion. For strictness, take $X=Y=\mathbb R$, $E=\mathbb R$, and $f(x)=e^x$. Then $f(\overline E)=(0,\infty)$, while $\overline{f(E)}=[0,\infty)$.

**Lean declarations:** `exercise02_closure_image_inclusion`, `exercise02_strict_inclusion`.

<a id="r04e03"></a>
### 4.3 — Closed zero sets
**Lean source:** [Exercise03.lean](../../Math/Rudin/Chapter04/Exercise03.lean).
**Inventory status:** Verified as stated.

**Statement.** For a continuous real function $f$ on a metric space $X$, the set $\{p\in X:f(p)=0\}$ is closed.

**Proof.** The singleton $\{0\}$ is closed in $\mathbb R$, and the stated set is its inverse image under the continuous map $f$.

**Lean declarations:** `exercise03_zero_set_closed`.

<a id="r04e04"></a>
### 4.4 — Continuous maps on dense sets
**Lean source:** [Exercise04.lean](../../Math/Rudin/Chapter04/Exercise04.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $f,g:X\to Y$ be continuous maps between metric spaces, and let $E$ be dense in $X$. Then $f(E)$ is dense in the subspace $f(X)$. If $f=g$ on $E$, then $f=g$ on $X$.

**Proof.** Since $\overline E=X$, Exercise 4.2 gives $f(X)\subseteq\overline{f(E)}$, where this closure is taken in $Y$. Intersecting with $f(X)$ proves density in the range, not necessarily in all of $Y$. The equalizer $\{x:f(x)=g(x)\}$ is closed, because the diagonal of the metric space $Y$ is closed. If it contains $E$, it contains $\overline E=X$.

**Lean declarations:** `exercise04_image_density`, `exercise04_dense_uniqueness`.

<a id="r04e05"></a>
### 4.5 — Extension from a closed set
**Lean source:** [Exercise05.lean](../../Math/Rudin/Chapter04/Exercise05.lean).
**Inventory status:** Verified as stated.

**Statement.** If $E\subseteq\mathbb R$ is closed and $f:E\to\mathbb R$ is continuous, there is a continuous $g:\mathbb R\to\mathbb R$ with $g|_E=f$. The same conclusion holds for values in $\mathbb R^k$, including $k=0$. Closedness of $E$ cannot be omitted.

**Scope.** The Lean results also allow any metric space $X$ in place of the ambient real line. They use the Tietze extension theorem rather than the suggested piecewise-affine construction. Empty closed domains are included.

**Proof.** A metric space is normal. The real-valued Tietze extension theorem therefore extends every continuous $f:E\to\mathbb R$ from a closed subset to the whole space, with no boundedness assumption on $f$. For $E=\varnothing$, one may simply take $g=0$. For an $\mathbb R^k$-valued function, extend each continuous coordinate by this theorem and assemble the extensions. Continuity of the coordinates gives continuity in the Euclidean topology. In dimension zero there is only one possible value.

For failure without closedness, take $E=(0,\infty)$ and $f(x)=1/x$. This is continuous on $E$, which is not closed because $0\in\overline E\setminus E$. If a continuous extension $g$ existed, the closed set $\{x:xg(x)=1\}$ would contain $(0,\infty)$ and hence zero. This would imply $0=1$.

**Lean declarations:** `exercise05_real_extension`, `exercise05_nonclosed_failure`, `exercise05_vector_extension`.

<a id="r04e06"></a>
### 4.6 — Compact graphs and continuity
**Lean source:** [Exercise06.lean](../../Math/Rudin/Chapter04/Exercise06.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $E$ be a compact metric space, $Y$ a metric space, and $f:E\to Y$ any map. Then $f$ is continuous if and only if its graph

$$
\Gamma_f=\{(x,f(x)):x\in E\}\subseteq E\times Y
$$

is compact. The empty domain is allowed. The implication from compact graph to continuity does not require a separate compactness assumption on $E$.

**Proof.** If $f$ is continuous, the map $x\mapsto(x,f(x))$ is continuous, so its image of the compact domain is compact. Conversely, suppose $\Gamma_f$ is compact. For every closed $F\subseteq Y$, the set $\Gamma_f\cap(E\times F)$ is compact. Its projection onto $E$ is exactly $f^{-1}(F)$, hence is compact and therefore closed in the metric space $E$. The closed-inverse-image criterion proves continuity.

**Lean declarations:** `exercise06_continuous_graph_compact`, `exercise06_compact_graph_continuous`, `exercise06_graph_equivalence`.

<a id="r04e07"></a>
### 4.7 — Continuity on lines is insufficient
**Lean source:** [Exercise07.lean](../../Math/Rudin/Chapter04/Exercise07.lean).
**Inventory status:** Verified as stated.

**Statement.** Define $f(0,0)=g(0,0)=0$ and, away from the origin, set

$$
f(x,y)=\frac{xy^2}{x^2+y^4},\qquad g(x,y)=\frac{xy^2}{x^2+y^6}.
$$

Then $|f|\le\tfrac12$ on $\mathbb R^2$, but $f$ is not continuous at the origin. For every neighborhood $U$ of the origin and every real $M$, some $p\in U$ satisfies $|g(p)|>M$. Nevertheless, the restriction of each function to every affine straight line is continuous everywhere on that line.

**Proof.** The denominators are positive away from the origin. The inequality

$$
0\le(|x|-y^2)^2=x^2+y^4-2|x|y^2
$$

gives $|f(x,y)|\le\tfrac12$ there, and the same bound holds at zero. It also bounds the distance between any two values by $1$, so the range is bounded. Along $(x,y)=(t^2,t)$ with $t\ne0$, $f=\tfrac12$, which contradicts continuity at the origin. Along $(x,y)=(t^3,t)$, $g=1/(2t)$. Taking positive $t$ sufficiently small puts this point in any prescribed $U$ and makes $|g|$ larger than any prescribed $M$.

Both functions are continuous away from the origin by the quotient rule for continuous functions. For a line through the origin with direction $v=(a,b)$, if $a=0$ both restrictions are identically zero. If $a\ne0$, cancellation gives, including their assigned values at $t=0$,

$$
f(ta,tb)=\frac{ab^2t}{a^2+t^2b^4},\qquad
 g(ta,tb)=\frac{ab^2t}{a^2+t^4b^6}.
$$

Both expressions are continuous at zero. An affine line that reaches zero at parameter $c$ can be written there as $(t-c)v$, so this argument applies at that point as well. All its other points use ordinary continuity away from zero. For $v\ne0$, one nonzero coordinate recovers the parameter continuously by $t=(p_i-a_i)/v_i$; thus the result is also continuity in the line's subspace topology. The case $v=0$ is a singleton and is immediate.

**Lean declarations:** `exercise07_f_bounded`, `exercise07_f_range_bounded`, `exercise07_g_locally_unbounded`, `exercise07_f_discontinuous`, `exercise07_f_line_continuity`, `exercise07_f_line_restriction`, `exercise07_g_line_continuity`, `exercise07_g_line_restriction`.

<a id="r04e08"></a>
### 4.8 — Uniform continuity on a bounded real domain
**Lean source:** [Exercise08.lean](../../Math/Rudin/Chapter04/Exercise08.lean).
**Inventory status:** Verified as stated.

**Statement.** If $E\subseteq\mathbb R$ is bounded and $f:E\to\mathbb R$ is uniformly continuous, then $f(E)$ is bounded. Equivalently, this holds for a real function uniformly continuous on $E$. It can fail when $E$ is unbounded.

**Proof.** A bounded subset of $\mathbb R$ is totally bounded: its closure is compact. Choose a uniform-continuity radius $\delta>0$ for output tolerance $1$. A finite collection of $\delta$-balls with centers in $E$ covers $E$, so the values of $f$ lie within distance $1$ of finitely many center values. This is a bounded set. If $E$ is empty, its image is empty and bounded. Without boundedness, use $E=\mathbb R$ and $f(x)=x$: the identity is uniformly continuous, but both domain and image are unbounded.

**Lean declarations:** `exercise08_bounded_image`, `exercise08_bounded_image_on`, `exercise08_unbounded_domain`.

<a id="r04e09"></a>
### 4.9 — Uniform continuity through diameters
**Lean source:** [Exercise09.lean](../../Math/Rudin/Chapter04/Exercise09.lean).
**Inventory status:** Verified as stated.

**Statement.** For metric spaces $X,Y$ and a map $f:X\to Y$, uniform continuity is equivalent to the following condition: for every real $\varepsilon>0$ there is a real $\delta>0$ such that, for every subset $E\subseteq X$,

$$
\operatorname{diam}E<\delta\quad\Longrightarrow\quad
\operatorname{diam}f(E)<\varepsilon.
$$

**Diameter convention.** The source's earlier diameter definition covers nonempty sets only. To make the displayed all-subsets condition precise, use the extended nonnegative diameter

$$
\operatorname{diam}E=\sup\{d(x,y):x,y\in E\}\in[0,\infty],
$$

with $\operatorname{diam}\varnothing=0$ and diameter $\infty$ for unbounded sets. For every nonempty bounded $E$, this equals the ordinary real supremum in the source, embedded in $[0,\infty]$. This is a notation extension, not a refutation. In particular, an unbounded set is not assigned real diameter zero.

**Proof.** The supremum of the empty family in $[0,\infty]$ is zero. If the pairwise distances of a nonempty set had a finite upper bound, fixing one point would put the entire set in a bounded ball. Thus an unbounded set has infinite extended diameter. For a nonempty bounded set, its pairwise-distance set is nonempty, bounded above, and nonnegative. Its real least upper bound is therefore also its least upper bound in $[0,\infty]$, proving agreement with the source definition.

Suppose $f$ is uniformly continuous. Given $\varepsilon>0$, choose $\delta>0$ for output tolerance $\varepsilon/2$. If $\operatorname{diam}E<\delta$, every $x,y\in E$ has $d(x,y)<\delta$, so $d(f(x),f(y))<\varepsilon/2$. Taking the supremum gives

$$
\operatorname{diam}f(E)\le\varepsilon/2<\varepsilon.
$$

The smaller tolerance is necessary to retain a strict conclusion after taking a supremum. The empty set satisfies the conclusion automatically; unbounded sets cannot satisfy the finite input bound.

Conversely, apply the diameter condition to $E=\{x,y\}$. Its diameter is $d(x,y)$, including when $x=y$, and the image diameter is $d(f(x),f(y))$. The resulting estimate is precisely uniform continuity.

**Lean declarations:** `exercise09_uniform_to_diameter`, `exercise09_diameter_to_uniform`, `exercise09_diameter_empty`, `exercise09_diameter_unbounded`, `exercise09_diameter_agrees`.

<a id="r04e10"></a>
### 4.10 — A sequential proof of uniform continuity
**Lean source:** [Exercise10.lean](../../Math/Rudin/Chapter04/Exercise10.lean).
**Inventory status:** Verified as stated.

**Statement.** If a map $f:X\to Y$ between metric spaces is not uniformly continuous, there are $\varepsilon>0$ and sequences $p_n,q_n\in X$ with

$$
d_X(p_n,q_n)\longrightarrow0,\qquad
 d_Y(f(p_n),f(q_n))>\varepsilon\quad\text{for every }n.
$$

Use these sequences to prove that a continuous map from a compact metric space is uniformly continuous.

**Proof.** Failure of uniform continuity gives $e>0$ such that for every $\delta>0$ some $p,q$ satisfy $d_X(p,q)<\delta$ and $d_Y(f(p),f(q))\ge e$. Choose these points for $\delta=1/(n+1)$ and set $\varepsilon=e/2$. This proves both required sequence estimates, including strict output separation.

Now suppose $X$ is compact and $f$ continuous. A subsequence $p_{n_j}$ converges to some $x\in X$. The triangle inequality and $d_X(p_{n_j},q_{n_j})\to0$ show that $q_{n_j}\to x$ too. Continuity gives $f(p_{n_j})\to f(x)$ and $f(q_{n_j})\to f(x)$, so their mutual distances tend to zero. This contradicts the fixed lower bound $\varepsilon$.

**Lean declarations:** `exercise10_nonuniform_sequences`, `exercise10_compact_uniform_continuity`.

<a id="r04e11"></a>
### 4.11 — Cauchy images and extension by limits
**Lean source:** [Exercise11.lean](../../Math/Rudin/Chapter04/Exercise11.lean).
**Inventory status:** Verified as stated.

**Statement.** A uniformly continuous map $f:X\to Y$ between metric spaces sends Cauchy sequences to Cauchy sequences. Consequently, if $E$ is dense in a metric space $X$ and $f:E\to\mathbb R$ is uniformly continuous, then $f$ has a continuous extension to $X$.

**Scope.** The sequence construction in the file works for every complete metric target $Y$ and gives a uniformly continuous extension. No completeness of $X$ is required.

**Proof.** Given an output tolerance $\varepsilon>0$, uniform continuity supplies $\delta>0$. A Cauchy sequence has all sufficiently late pairs within $\delta$, so its image has all sufficiently late pairs within $\varepsilon$.

For each $x\in X$, choose $u_n\in E$ tending to $x$, using density. The sequence is Cauchy in $E$, so $f(u_n)$ is Cauchy and has a limit in the complete target. Define $g(x)$ to be this limit. If $v_n\in E$ also tends to $x$, then $d(u_n,v_n)\to0$; uniform continuity gives $d(f(u_n),f(v_n))\to0$. Hence the two limits agree, so $g$ is independent of the choices. At $x\in E$, comparison with the constant sequence $x$ proves $g(x)=f(x)$.

To prove uniform continuity, choose $\delta$ for the original map with tolerance $\varepsilon/2$. If $d(x,y)<\delta$, approximating sequences $u_n\to x$ and $v_n\to y$ eventually satisfy $d(u_n,v_n)<\delta$. Thus their image distances are eventually at most $\varepsilon/2$. Passing to limits gives $d(g(x),g(y))\le\varepsilon/2<\varepsilon$. In particular $g$ is continuous. If $X$ is empty, the unique map gives the extension; density permits no nonempty $X$ with $E$ empty.

**Lean declarations:** `exercise11_cauchy_images`, `exercise11_extension_via_sequences`, `exercise11_extension_uniformContinuous`.

<a id="r04e12"></a>
### 4.12 — Composition of uniformly continuous maps
**Lean source:** [Exercise12.lean](../../Math/Rudin/Chapter04/Exercise12.lean).
**Inventory status:** Verified as stated.

**Statement.** If $X,Y,Z$ are metric spaces and $f:X\to Y$, $g:Y\to Z$ are uniformly continuous, then $g\circ f:X\to Z$ is uniformly continuous.

**Proof.** Given $\varepsilon>0$, choose $\eta>0$ such that $d_Y(u,v)<\eta$ implies $d_Z(g(u),g(v))<\varepsilon$. Then choose $\delta>0$ such that $d_X(x,y)<\delta$ implies $d_Y(f(x),f(y))<\eta$. Combining the implications proves the claim.

**Lean declarations:** `exercise12_composition`.

<a id="r04e13"></a>
### 4.13 — Which targets admit dense-domain extensions?
**Lean source:** [Exercise13.lean](../../Math/Rudin/Chapter04/Exercise13.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $E$ be dense in a metric space $X$ and let $f:E\to\mathbb R$ be uniformly continuous. There is a unique continuous extension $g:X\to\mathbb R$. The extension also exists when the target is $\mathbb R^k$, any compact metric space, or any complete metric space. It need not exist for an arbitrary metric target. For a complete target, the extension is uniformly continuous and is unique among continuous extensions. No nonemptiness assumption is needed, and $k=0$ is allowed.

**Proof.** For any complete metric target, the sequence construction of Exercise 4.11 supplies a uniformly continuous extension. The real line and every finite-dimensional Euclidean space are complete. A compact metric space is complete as well: a Cauchy sequence has a convergent subsequence by compactness, and the Cauchy property makes the entire sequence converge to the same limit. This answers all three target generalizations affirmatively.

For uniqueness, two continuous extensions agree on dense $E$, so Exercise 4.4 makes them equal on $X$. This uniqueness argument works for every metric target, whether complete or not.

For the negative answer, let $X=\mathbb R$, $E=\mathbb R\setminus\{0\}$, and take the same punctured line as target $Y$, with its usual subspace metric. The identity $f:E\to Y$ is uniformly continuous and $E$ is dense. The sequence $1/(n+1)$ is Cauchy but has no limit in $Y$, so $Y$ is not complete. If $g:\mathbb R\to Y$ were a continuous extension, composing it with the inclusion $Y\hookrightarrow\mathbb R$ would give a continuous real map equal to the identity on $E$. Density forces it to be the identity everywhere, requiring $g(0)=0\notin Y$.

**Lean declarations:** `exercise13_real_extension`, `exercise13_uniqueness`, `exercise13_euclidean_range`, `exercise13_compact_range`, `exercise13_complete_range`, `exercise13_arbitrary_range`.

<a id="r04e14"></a>
### 4.14 — A fixed point in the unit interval
**Lean source:** [Exercise14.lean](../../Math/Rudin/Chapter04/Exercise14.lean).
**Inventory status:** Verified as stated.

**Statement.** Every continuous $f:[0,1]\to[0,1]$ has a fixed point, possibly an endpoint.

**Proof.** The continuous real function $F(x)=f(x)-x$ on $[0,1]$ satisfies $F(0)\ge0$ and $F(1)\le0$. If either value is zero, that endpoint is fixed. Otherwise, the intermediate value theorem gives $c\in(0,1)$ with $F(c)=0$, hence $f(c)=c$.

**Lean declarations:** `exercise14_fixed_point`.

<a id="r04e15"></a>
### 4.15 — Continuous open real maps are monotone
**Lean source:** [Exercise15.lean](../../Math/Rudin/Chapter04/Exercise15.lean).
**Inventory status:** Verified as stated.

**Statement.** A map is open if it sends every open set to an open set. Every continuous open map $f:\mathbb R\to\mathbb R$ is nondecreasing or nonincreasing. Neither injectivity nor surjectivity is assumed.

**Proof.** An open real map has no local maximum: an open neighborhood on which $f\le f(x)$ would have an open image containing $f(x)$ but no larger values, which is impossible. The same argument excludes local minima.

If $a<b$ and $f(a)=f(b)$, continuity on $[a,b]$ gives a local extremum in $(a,b)$. Indeed, if $f$ is constant there every interior point is an extremum; otherwise an attained maximum above the endpoint value or an attained minimum below it is interior. This contradicts openness. Thus $f$ is injective. The standard monotonicity theorem for continuous injections on a real interval now gives that $f$ is strictly increasing or strictly decreasing, and therefore has the required weak monotonicity.

**Lean declarations:** `exercise15_open_continuous_monotone`.

<a id="r04e16"></a>
### 4.16 — Integer and fractional parts
**Lean source:** [Exercise16.lean](../../Math/Rudin/Chapter04/Exercise16.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $[x]=\lfloor x\rfloor$ be the integer satisfying $x-1<[x]\le x$, regarded as real-valued, and let $\{x\}=x-[x]$, so $0\le\{x\}<1$. Both functions are continuous exactly at the nonintegers. At every integer $n$,

$$
[n]=n,\quad\lim_{x\to n^-}[x]=n-1,\quad\lim_{x\to n^+}[x]=n,
$$

$$
\{n\}=0,\quad\lim_{x\to n^-}\{x\}=1,\quad\lim_{x\to n^+}\{x\}=0.
$$

Thus all their discontinuities are simple jumps, and both functions are right-continuous at each integer. At a noninteger, both one-sided limits equal the function's value.

**Proof.** On $(n,n+1)$, the integer part is constantly $n$ and the fractional part is $x-n$. This proves continuity and the one-sided limits at nonintegers. Immediately to the left of $n$, the integer part is $n-1$, while on $[n,n+1)$ it is $n$. Subtracting these values from $x$ gives the asserted limits for the fractional part. The unequal left and right limits exclude continuity at every integer; the right-hand formulas include the endpoint values and prove right-continuity. The inequality $[x]\le x$ is non-strict, including at integers.

**Lean declarations:** `exercise16_floor_discontinuities`, `exercise16_floor_integer`, `exercise16_noninteger_limits`, `exercise16_fractional_discontinuities`, `exercise16_frac_integer`.

<a id="r04e17"></a>
### 4.17 — Countability of simple discontinuities
**Lean source:** [Exercise17.lean](../../Math/Rudin/Chapter04/Exercise17.lean).
**Inventory status:** Verified as stated.

**Statement.** For any real function on $(a,b)$, its simple discontinuities form an at most countable set. Here a simple discontinuity is an interior point at which both finite one-sided limits exist but the function is not continuous. This includes upward jumps, downward jumps, and removable discontinuities. No condition is imposed at $a$ or $b$.

**Proof.** At an upward jump $x$, write $L=f(x-)<f(x+)=R$. The source's rational-triple construction is as follows:

- **(a)** Choose $p\in\mathbb Q$ with $L<p<R$.
- **(b)** From the left limit, choose $q\in\mathbb Q$ with $a<q<x$ such that $f(t)<p$ whenever $q<t<x$.
- **(c)** From the right limit, choose $r\in\mathbb Q$ with $x<r<b$ such that $f(t)>p$ whenever $x<t<r$.

The same $p$ is used in all three steps. A triple $(p,q,r)$ can describe at most one point. If it described $x<y$, the midpoint $t=(x+y)/2$ would lie in both $(x,r)$ and $(q,y)$, forcing $f(t)>p$ and $f(t)<p$. Since $\mathbb Q^3$ is countable, upward jumps are at most countable. Apply the same result to $-f$ for downward jumps.

To treat removable discontinuities, first fix any set $S\subseteq\mathbb R$. Its points $x\in S$ for which some interval $(x,x+\eta_x)$ misses $S$ form a countable set. Choose a rational in each such interval. The intervals belonging to distinct such points are disjoint: if $x<y$ and $y\in S$, then $y\ge x+\eta_x$. Thus the chosen rationals distinguish the points.

If $f(x)$ is strictly below its finite right limit $R$, choose rational $p$ with $f(x)<p<R$. Then $x$ belongs to $S_p=\{t:f(t)<p\}$, but a right-hand interval at $x$ misses $S_p$. The preceding countability result and a countable union over $p$ show that these points are countable. Applying it to $-f$ treats $f(x)>R$. Hence all discrepancies between a value and a finite right limit are countable, including all removable discontinuities.

Finally, if the two finite one-sided limits are equal to each other and to $f(x)$, then $f$ is continuous at $x$. Every simple discontinuity therefore belongs to one of the three countable classes above. Since $x$ is interior to $(a,b)$, domain-relative one-sided limits agree with the usual local one-sided limits; the argument applies without any extension assumption outside the interval.

**Lean declarations:** `exercise17_a`, `exercise17_b`, `exercise17_c`, `exercise17_triple_uniqueness`, `exercise17_upward_jumps_countable`, `exercise17_other_simple_types`, `exercise17_simple_discontinuities_countable`, `exercise17_simple_discontinuities_within_countable`.

<a id="r04e18"></a>
### 4.18 — Thomae's function
**Lean source:** [Exercise18.lean](../../Math/Rudin/Chapter04/Exercise18.lean).
**Inventory status:** Verified as stated.

**Statement.** Define $f(x)=0$ for irrational $x$, and

$$
f(m/n)=1/n
$$

when $m,n\in\mathbb Z$, $n>0$, and $m,n$ are relatively prime. In particular, $f(0)=1$, using the reduced denominator $1$. Then $f$ is continuous at every irrational point and has a simple removable discontinuity at every rational point. In fact, its deleted limit at every real point is zero.

**Proof.** In any bounded interval there are only finitely many reduced rationals with denominator at most a fixed integer $N$: both the denominator and, by boundedness, the numerator range over finite sets. Given $x\in\mathbb R$ and $\varepsilon>0$, choose $N$ with $1/(N+1)<\varepsilon$ and a bounded neighborhood of $x$. Exclude from a smaller neighborhood the finitely many rationals in this bounded interval with denominator at most $N$, except possibly $x$ itself. Every remaining $y\ne x$ is irrational, giving $f(y)=0$, or has reduced denominator at least $N+1$, giving $0<f(y)\le1/(N+1)<\varepsilon$. This proves the deleted limit is zero. At an irrational point it equals $f(x)$, proving continuity. At a rational point both one-sided limits are zero, but $f(x)>0$; this is a simple removable discontinuity, including at zero.

**Lean declarations:** `exercise18_irrational_continuity`, `exercise18_rational_simple_discontinuity`, `exercise18_deleted_limit`.

<a id="r04e19"></a>
### 4.19 — Intermediate values and closed rational level sets
**Lean source:** [Exercise19.lean](../../Math/Rudin/Chapter04/Exercise19.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $f:\mathbb R\to\mathbb R$ have the intermediate value property: whenever $f(a)<c<f(b)$, some point strictly between $a$ and $b$, in either order, has value $c$. Suppose $\{x:f(x)=r\}$ is closed for each rational $r$. Then $f$ is continuous.

**Proof.** Fix $x$ and a rational $r\ne f(x)$. The complement of the closed $r$-level set contains an open interval about $x$. On that interval, $f$ must stay on the same side of $r$ as $f(x)$: a point on the other side would, by the intermediate value property on the segment joining it to $x$, produce a point of the excluded level set.

Given $\varepsilon>0$, choose rationals

$$
f(x)-\varepsilon<r<f(x)<s<f(x)+\varepsilon.
$$

Apply the preceding argument to both levels and intersect the resulting neighborhoods. On this intersection $r<f(y)<s$, so $|f(y)-f(x)|<\varepsilon$. Thus $f$ is continuous at every $x$.

**Lean declarations:** `exercise19_closed_rational_fibers`.

<a id="r04e20"></a>
### 4.20 — Distance to a nonempty set
**Lean source:** [Exercise20.lean](../../Math/Rudin/Chapter04/Exercise20.lean).
**Inventory status:** Verified as stated.

**Statement.** For a nonempty subset $E$ of a metric space $X$, define

$$
\rho_E(x)=\inf_{z\in E}d(x,z).
$$

Then **(a)** $\rho_E(x)=0$ if and only if $x\in\overline E$; and **(b)**

$$
|\rho_E(x)-\rho_E(y)|\le d(x,y)\qquad(x,y\in X).
$$

Consequently $\rho_E:X\to\mathbb R$ is uniformly continuous.

**Proof.** Nonemptiness and the lower bound zero make the infimum a finite nonnegative real number. It is zero exactly when, for every $\varepsilon>0$, some $z\in E$ has $d(x,z)<\varepsilon$. This is precisely the ball criterion for $x\in\overline E$, not necessarily for $x\in E$.

For every $z\in E$, the triangle inequality gives $d(x,z)\le d(x,y)+d(y,z)$. Taking infima gives $\rho_E(x)\le d(x,y)+\rho_E(y)$. Interchange $x,y$ to obtain the reverse difference bound, and combine them to obtain (b). Taking $\delta=\varepsilon$ proves uniform continuity. No assertion for an empty $E$ is needed or used.

**Lean declarations:** `exercise20_a`, `exercise20_b_lipschitz`, `exercise20_b_uniform_continuity`.

<a id="r04e21"></a>
### 4.21 — Positive separation from a compact set
**Lean source:** [Exercise21.lean](../../Math/Rudin/Chapter04/Exercise21.lean).
**Inventory status:** Verified as stated.

**Statement.** If $K,F$ are disjoint subsets of a metric space, $K$ is compact, and $F$ is closed, there is $\delta>0$ such that

$$
d(p,q)>\delta\qquad(p\in K,\ q\in F).
$$

This includes empty sets. The result can fail for two disjoint closed noncompact sets.

**Proof.** If either set is empty, any positive $\delta$, for example $1$, works vacuously. Otherwise, the continuous function $\rho_F$ attains its minimum $m$ on $K$. At its minimizer $p_0$, closedness and disjointness give $p_0\notin\overline F=F$, hence $m>0$. For every $p\in K$, $q\in F$,

$$
d(p,q)\ge\rho_F(p)\ge m>m/2.
$$

Thus choose $\delta=m/2$, retaining the requested strict inequality.

For the counterexample, use $\mathbb R^2$ with its product maximum metric, and let

$$
A=\{(x,y):y=0\},\qquad B=\{(x,y):xy=1\}.
$$

They are closed as level sets of continuous functions and are disjoint. Both have unbounded first coordinate, so neither is compact. For any $\delta>0$, put $t=2/\delta$. The points $(t,0)\in A$ and $(t,t^{-1})\in B$ have distance $t^{-1}=\delta/2<\delta$. Hence no positive uniform lower bound exists. The same distances occur in the Euclidean metric.

**Lean declarations:** `exercise21_positive_separation`, `exercise21_closed_noncompact_failure`.

<a id="r04e22"></a>
### 4.22 — Separating closed sets by a continuous function
**Lean source:** [Exercise22.lean](../../Math/Rudin/Chapter04/Exercise22.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $A,B$ be disjoint nonempty closed subsets of a metric space $X$, and set

$$
f(p)=\frac{\rho_A(p)}{\rho_A(p)+\rho_B(p)}.
$$

The denominator is positive everywhere; $f$ is continuous, $0\le f\le1$, $f^{-1}(\{0\})=A$, and $f^{-1}(\{1\})=B$. Every closed subset of $X$ is the zero set of a continuous real function. Moreover,

$$
V=f^{-1}([0,1/2)),\qquad W=f^{-1}((1/2,1])
$$

are disjoint open sets containing $A$ and $B$, respectively. Thus any two disjoint closed subsets of $X$, including empty ones, have disjoint open neighborhoods.

**Proof.** Both distance functions are nonnegative and continuous by Exercise 4.20. Their sum could be zero only if both were zero, placing $p$ in $A\cap B$ by closedness. Hence the denominator is positive and the quotient is continuous. Its numerator lies between zero and its denominator, giving $0\le f\le1$. With a positive denominator, $f(p)=0$ is equivalent to $\rho_A(p)=0$, hence to $p\in A$; and $f(p)=1$ is equivalent to $\rho_B(p)=0$, hence to $p\in B$.

For a nonempty closed set $C$, use $h=\rho_C$ to represent it as a zero set. For $C=\varnothing$, use $h=1$; for $C=X$, the constant zero function also gives the result, including when $X$ is empty.

The half-open intervals displayed above are not open in $\mathbb R$. Instead use the established range bound to write $V=\{p:f(p)<1/2\}$ and $W=\{p:f(p)>1/2\}$. These are open by continuity. Their defining inequalities are incompatible, and the zero and one fibers give $A\subseteq V$ and $B\subseteq W$. Finally, if $A$ is empty, choose $V=\varnothing$, $W=X$; if $B$ is empty, choose $V=X$, $W=\varnothing$. These choices complete the separation claim for arbitrary disjoint closed sets.

**Lean declarations:** `exercise22_denominator_positive`, `exercise22_continuous`, `exercise22_range`, `exercise22_zero_fiber`, `exercise22_one_fiber`, `exercise22_all_closed_zero_sets`, `exercise22_open_neighborhoods`, `exercise22_disjoint_neighborhoods`, `exercise22_normality`.

<a id="r04e23"></a>
### 4.23 — Continuity and slopes of convex functions
**Lean source:** [Exercise23.lean](../../Math/Rudin/Chapter04/Exercise23.lean).
**Inventory status:** Verified as stated.

**Statement.** Suppose $f:(a,b)\to\mathbb R$ is convex in the source sense:

$$
f(\lambda x+(1-\lambda)y)\le\lambda f(x)+(1-\lambda)f(y)
\quad(x,y\in(a,b),\ 0<\lambda<1).
$$

Then $f$ is continuous on $(a,b)$. If $f$ is convex on an interval $S$, $h$ is convex and nondecreasing on an interval $T$, and $f(S)\subseteq T$, then $h\circ f$ is convex on $S$. In particular, $e^f$ is convex. For $a<s<t<u<b$,

$$
\frac{f(t)-f(s)}{t-s}\le\frac{f(u)-f(s)}{u-s}
\le\frac{f(u)-f(t)}{u-t}.
$$

**Proof.** The endpoint weights $0,1$ give equality, so the strict-weight definition also gives the usual closed-weight definition. Express

$$
t=\frac{u-t}{u-s}s+\frac{t-s}{u-s}u.
$$

Convexity gives $(u-s)f(t)\le(u-t)f(s)+(t-s)f(u)$. Rearranging this inequality and dividing by the positive factors gives each displayed slope inequality.

Fix $x\in(a,b)$ and choose $r<x<s$ inside the interval. The slope inequalities imply, for $r<y<s$ and $y\ne x$,

$$
\frac{f(x)-f(r)}{x-r}\le\frac{f(y)-f(x)}{y-x}
\le\frac{f(s)-f(x)}{s-x}.
$$

For $y<x$, the middle quotient is the same secant slope with endpoints $y,x$; the same inequalities apply. The absolute value of this quotient is bounded by the maximum of the absolute values of the two fixed outer slopes. Thus $|f(y)-f(x)|\le M|y-x|$ locally, proving continuity at $x$. No endpoint continuity is asserted.

For composition, put $z=\lambda x+(1-\lambda)y$. Both $f(z)$ and $\lambda f(x)+(1-\lambda)f(y)$ lie in $T$. First apply monotonicity of $h$ to the convexity inequality for $f$, and then apply convexity of $h$:

$$
h(f(z))\le h(\lambda f(x)+(1-\lambda)f(y))
\le\lambda h(f(x))+(1-\lambda)h(f(y)).
$$

The exponential is convex and increasing on all of $\mathbb R$, so it is an allowed outer function. The file also allows arbitrary convex sets $S,T\subseteq\mathbb R$, including degenerate or empty intervals.

**Lean declarations:** `exercise23_convex_continuity`, `exercise23_increasing_convex_composition`, `exercise23_exp_convex`, `exercise23_first_slope_inequality`, `exercise23_second_slope_inequality`.

<a id="r04e24"></a>
### 4.24 — Continuous midpoint-convex functions are convex
**Lean source:** [Exercise24.lean](../../Math/Rudin/Chapter04/Exercise24.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $f:(a,b)\to\mathbb R$ be continuous and suppose

$$
f((x+y)/2)\le\frac{f(x)+f(y)}2\qquad(x,y\in(a,b)).
$$

Then $f$ is convex: for every $x,y\in(a,b)$ and $0\le\lambda\le1$,

$$
f(\lambda x+(1-\lambda)y)\le\lambda f(x)+(1-\lambda)f(y).
$$

This includes the source's strictly interior weights and requires no continuity at $a$ or $b$.

**Proof.** First let $g$ be continuous and midpoint-convex on $[0,1]$ with $g(0)=g(1)=0$. It attains a maximum $M=g(c)$. If $c\le1/2$, then

$$
M=g((0+2c)/2)\le\frac{g(0)+g(2c)}2\le M/2.
$$

If $c\ge1/2$, apply midpoint convexity to $2c-1$ and $1$ to obtain the same inequality. Thus $M\le0$, so $g\le0$ throughout $[0,1]$.

For fixed $x,y\in(a,b)$, apply this result to

$$
g(t)=f(tx+(1-t)y)-tf(x)-(1-t)f(y).
$$

The whole segment lies inside $(a,b)$, so $g$ is continuous on $[0,1]$. The affine maps in this formula preserve midpoints; the hypothesis on $f$ therefore makes $g$ midpoint-convex. Its endpoint values are zero. Hence $g(\lambda)\le0$, which is the required convexity inequality, including $\lambda=0,1$ and $x=y$.

**Lean declarations:** `exercise24_midpoint_to_convex`, `exercise24_source`.

<a id="r04e25"></a>
### 4.25 — Sums of closed sets
**Lean source:** [Exercise25.lean](../../Math/Rudin/Chapter04/Exercise25.lean).
**Inventory status:** Verified as stated.

**Statement.** For subsets of $\mathbb R^k$, let $A+B=\{x+y:x\in A,\ y\in B\}$. **(a)** If $K$ is compact and $C$ is closed, then $K+C$ is closed, including empty summands and $k=0$. **(b)** For an irrational real $\alpha$, the sets

$$
C_1=\mathbb Z,\qquad C_2=\{n\alpha:n\in\mathbb Z\}
$$

are closed, but $C_1+C_2$ is countably infinite, dense in $\mathbb R$, and not closed. Countable infinitude of this sum holds for every real $\alpha$.

**Proof.** For (a), suppose $z_n=k_n+c_n\in K+C$ converges to $z$. Compactness supplies a subsequence $k_{n_j}\to k\in K$. Then $c_{n_j}=z_{n_j}-k_{n_j}\to z-k$, and closedness gives $z-k\in C$. Therefore $z\in K+C$. The sequential closedness criterion applies in Euclidean space. If either summand is empty, the sum is empty and closed; dimension zero causes no change to the argument.

For (b), $\mathbb Z$ is closed in $\mathbb R$, since every noninteger has an open interval around it containing no integer. Irrationality implies $\alpha\ne0$, so multiplication by $\alpha$ is a homeomorphism and sends $\mathbb Z$ to the closed set $C_2$. The sum is the image of the countable set $\mathbb Z^2$ under $(m,n)\mapsto m+n\alpha$; it contains $\mathbb Z$ and hence is infinite, for any $\alpha$.

To see density for irrational $\alpha$, the pigeonhole principle applied to the fractional parts of $0,\alpha,\ldots,N\alpha$ gives distinct indices whose fractional parts differ by less than $1/N$. Their difference is a nonzero element of $\mathbb Z+\alpha\mathbb Z$; it cannot be zero because $\alpha$ is irrational. Taking its absolute value gives a positive element $\eta<1/N$ of this additive subgroup. Integer multiples of $\eta$ approximate any real number with error less than $\eta$. Since $N$ can be arbitrarily large, the subgroup is dense. This is the standard irrational-generator density result used in the Lean proof. If the sum were also closed, density would make it all of $\mathbb R$, contradicting its countability and the uncountability of $\mathbb R$.

**Lean declarations:** `exercise25_a`, `exercise25_b_first_closed`, `exercise25_b_second_closed`, `exercise25_b_countable_sum`, `exercise25_b_dense_sum`, `exercise25_b_nonclosed_sum`.

<a id="r04e26"></a>
### 4.26 — Recovering continuity through an injective map
**Lean source:** [Exercise26.lean](../../Math/Rudin/Chapter04/Exercise26.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $X,Y,Z$ be metric spaces with $Y$ compact, let $f:X\to Y$ be arbitrary, and let $g:Y\to Z$ be continuous and injective. Put $h=g\circ f$. If $h$ is uniformly continuous, then $f$ is uniformly continuous; if $h$ is continuous, then $f$ is continuous. Compactness of $Y$ is necessary, even when $X$ and $Z$ are compact. The file also proves the forward implications: uniformly continuous $f$ gives uniformly continuous $h$ under compactness of $Y$, and continuous $f$ gives continuous $h$ without compactness or injectivity assumptions on $g$.

**Proof.** A continuous injection from a compact space to a metric space is a homeomorphism onto its image: it maps closed sets, which are compact, to compact and therefore closed sets. Thus the inverse $g^{-1}:g(Y)\to Y$ is continuous. The image $g(Y)$ is compact, so this inverse is uniformly continuous by the compact-domain uniform-continuity theorem. Regard $h$ as a map into the subspace $g(Y)$; its continuity or uniform continuity is unchanged. The identity $f=g^{-1}\circ h$ and composition give the two asserted implications. For the forward directions, use continuity of compositions; in the uniform case $g$ itself is uniformly continuous because $Y$ is compact.

For both failures without compactness, take $X=Z=[0,1]$ with the usual metric and let $Y$ be the same underlying set with the discrete zero-one metric. Let $f:X\to Y$ and $g:Y\to Z$ both be the identity on points. The space $Y$ is infinite and discrete, hence not compact: its cover by singleton open sets has no finite subcover. Every map from a discrete space is continuous, so $g$ is continuous and injective. The composite $h$ is the usual identity on $[0,1]$, hence uniformly continuous and continuous. But $f$ cannot be continuous, since its image of compact $X$ would be all of the noncompact space $Y$. It is consequently not uniformly continuous either. Both outer spaces remain compact, as required.

**Lean declarations:** `exercise26_uniform_continuity`, `exercise26_continuity`, `exercise26_noncompact_uniform_failure`, `exercise26_noncompact_continuity_failure`, `exercise26_uniform_continuity_forward`, `exercise26_continuity_forward`.

<a id="chapter-05"></a>

## Chapter 5 — Differentiation

**Exercises:** [1](#r05e01) · [2](#r05e02) · [3](#r05e03) · [4](#r05e04) · [5](#r05e05) · [6](#r05e06) · [7](#r05e07) · [8](#r05e08) · [9](#r05e09) · [10](#r05e10) · [11](#r05e11) · [12](#r05e12) · [13](#r05e13) · [14](#r05e14) · [15](#r05e15) · [16](#r05e16) · [17](#r05e17) · [18](#r05e18) · [19](#r05e19) · [20](#r05e20) · [21](#r05e21) · [22](#r05e22) · [23](#r05e23) · [24](#r05e24) · [25](#r05e25) · [26](#r05e26) · [27](#r05e27) · [28](#r05e28) · [29](#r05e29)

<a id="r05e01"></a>
### 5.1 — A quadratic difference bound forces constancy
**Lean source:** [Exercise01.lean](../../Math/Rudin/Chapter05/Exercise01.lean).
**Inventory status:** Verified as stated.
**Statement.** Suppose $f:\mathbb R\to\mathbb R$ satisfies $|f(x)-f(y)|\le (x-y)^2$ for all real $x,y$. Then $f$ is constant.

**Proof.** For $y\ne x$,

$$
\left|\frac{f(y)-f(x)}{y-x}\right|\le |y-x|\longrightarrow0.
$$

Hence $f'(x)=0$ at every real $x$. The mean value theorem on the interval between any two points gives equal function values.

**Lean declarations:** `exercise01_constant`.

<a id="r05e02"></a>
### 5.2 — An increasing function and its inverse derivative
**Lean source:** [Exercise02.lean](../../Math/Rudin/Chapter05/Exercise02.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $f$ be real-valued and differentiable on $(a,b)$, with $f'(x)>0$ there. Then $f$ is strictly increasing. Its inverse $g:f((a,b))\to(a,b)$ satisfies $g(f(x))=x$ and $f(g(y))=y$. The image is open, $g$ is differentiable on it, and

$$
g'(f(x))=\frac1{f'(x)}\qquad(a<x<b).
$$

No continuity of $f'$ is assumed.

**Proof.** The mean value theorem gives $f(v)>f(u)$ when $a<u<v<b$, so the inverse is well-defined. For each $x\in(a,b)$ choose $a<l<x<r<b$. Continuity and strict increase give $f((l,r))=(f(l),f(r))$, an open neighborhood of $f(x)$ inside the image. This also proves inverse continuity: points close enough to $f(x)$ have inverse values between any prescribed nearby $l$ and $r$. Put $y=f(t)$. As $y\to f(x)$, inverse continuity gives $t\to x$, and

$$
\frac{g(y)-g(f(x))}{y-f(x)}
=\left(\frac{f(t)-f(x)}{t-x}\right)^{-1}
\longrightarrow\frac1{f'(x)}.
$$

The denominator limit is positive. Any extension of $g$ outside the image has the same local derivative at these image points. If $(a,b)$ is empty, the interval assertions are vacuous.

**Lean declarations:** `exercise02_strict_increase`, `exercise02_inverse_identities`, `exercise02_inverse_hasDerivAt`, `exercise02_inverse_derivative`.

<a id="r05e03"></a>
### 5.3 — Sharp parameters for an injective perturbation
**Lean source:** [Exercise03.lean](../../Math/Rudin/Chapter05/Exercise03.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $g:\mathbb R\to\mathbb R$ be differentiable and satisfy $|g'(x)|\le M$ everywhere. For every $\varepsilon>0$ with $\varepsilon M<1$, the function $x\mapsto x+\varepsilon g(x)$ is strictly increasing and hence injective. If $M=0$, every positive $\varepsilon$ works. If $M>0$, the range is $0<\varepsilon<1/M$, and this is sharp as a guarantee based only on $M$.

**Proof.** The hypothesis forces $M\ge0$, and

$$
1+\varepsilon g'(x)\ge1-\varepsilon M>0.
$$

The mean value theorem proves strict increase. The choice $\varepsilon=1/(M+1)$ always lies in the stated range. Conversely, if $\varepsilon>0$ and $\varepsilon M\ge1$, take $g(x)=-x/\varepsilon$. Then $|g'|=1/\varepsilon\le M$, but $x+\varepsilon g(x)=0$ for every $x$. This includes the excluded endpoint $\varepsilon=1/M$.

**Lean declarations:** `exercise03_admissible_zero`, `exercise03_admissible_pos`, `exercise03_admissible_nonempty`, `exercise03_sharp`, `exercise03_injectivity`.

<a id="r05e04"></a>
### 5.4 — A polynomial root from a coefficient identity
**Lean source:** [Exercise04.lean](../../Math/Rudin/Chapter05/Exercise04.lean).
**Inventory status:** Verified as stated.
**Statement.** If $n\ge0$ is an integer and real $C_0,\ldots,C_n$ satisfy $\sum_{k=0}^n C_k/(k+1)=0$, then $\sum_{k=0}^n C_kx^k=0$ for some $0<x<1$.

**Proof.** Set $P(t)=\sum_{k=0}^n C_kt^{k+1}/(k+1)$. Then $P(0)=P(1)=0$ and $P'(t)=\sum_{k=0}^n C_kt^k$. Rolle's theorem gives the required interior root. This proof includes $n=0$ and the zero polynomial; no nonzero-coefficient assumption is needed.

**Lean declarations:** `exercise04_interior_root`.

<a id="r05e05"></a>
### 5.5 — Vanishing derivatives give vanishing unit increments
**Lean source:** [Exercise05.lean](../../Math/Rudin/Chapter05/Exercise05.lean).
**Inventory status:** Verified as stated.
**Statement.** If $f:(0,\infty)\to\mathbb R$ is differentiable and $f'(x)\to0$ as $x\to\infty$, then $f(x+1)-f(x)\to0$.

**Proof.** For every $x>0$, the mean value theorem gives $c_x\in(x,x+1)$ with $f(x+1)-f(x)=f'(c_x)$. Given $\varepsilon>0$, choose $R$ so that $|f'(t)|<\varepsilon$ for $t\ge R$. For $x\ge\max(R,1)$, $c_x>R$, so the increment has absolute value less than $\varepsilon$. No limit of $f$ itself is required.

**Lean declarations:** `exercise05_increment_limit`.

<a id="r05e06"></a>
### 5.6 — Monotonicity of slopes from the origin
**Lean source:** [Exercise06.lean](../../Math/Rudin/Chapter05/Exercise06.lean).
**Inventory status:** Verified as stated.
**Statement.** Suppose $f$ is continuous on $[0,\infty)$, differentiable on $(0,\infty)$, $f(0)=0$, and $f'$ is nondecreasing on $(0,\infty)$. Then $f(x)/x$ is nondecreasing for $x>0$.

**Proof.** The derivative criterion for convexity, with continuity at the endpoint, makes $f$ convex on $[0,\infty)$. For $0<x\le y$, write $x=(1-x/y)0+(x/y)y$. Convexity gives $f(x)\le(x/y)f(y)$, because $f(0)=0$. Division by $x>0$ proves the claim. No derivative at zero is assumed. The four source labels describe hypotheses, not four separate conclusions.

**Lean declarations:** `exercise06_quotient_monotonicity`.

<a id="r05e07"></a>
### 5.7 — Quotients at a common simple zero
**Lean source:** [Exercise07.lean](../../Math/Rudin/Chapter05/Exercise07.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $f,g$ be real- or complex-valued functions of a real variable, differentiable at $x$. Suppose $f(x)=g(x)=0$, $f'(x)=A$, and $g'(x)=B\ne0$. Then $g(t)\ne0$ in a sufficiently small punctured neighborhood of $x$, and

$$
\lim_{t\to x}\frac{f(t)}{g(t)}=\frac AB.
$$

For complex values, derivatives are with respect to the real parameter.

**Proof.** The slopes $f(t)/(t-x)$ and $g(t)/(t-x)$ tend to $A$ and $B$. Since $B\ne0$, the second slope, and therefore $g(t)$, is eventually nonzero for $t\ne x$. Their quotient tends to $A/B$ and equals $f(t)/g(t)$. This argument uses only field operations and limits, so it applies to both $\mathbb R$ and $\mathbb C$.

**Lean declarations:** `exercise07_real_quotient_limit`, `exercise07_complex_quotient_limit`.

<a id="r05e08"></a>
### 5.8 — Uniform differentiability on a closed interval
**Lean source:** [Exercise08.lean](../../Math/Rudin/Chapter05/Exercise08.lean).
**Inventory status:** Verified as stated.
**Statement.** Suppose $f:[a,b]\to\mathbb R$ has a derivative $d(x)$ within $[a,b]$ at every point, and $d$ is continuous on $[a,b]$. For every $\varepsilon>0$ there is $\delta>0$ such that

$$
\left|\frac{f(t)-f(x)}{t-x}-d(x)\right|<\varepsilon
$$

whenever $x,t\in[a,b]$ and $0<|t-x|<\delta$. The same result holds for $f:[a,b]\to\mathbb R^k$, with scalar division of vectors and Euclidean norm. In fact, the proof works in any real normed space. Endpoint derivatives are one-sided.

**Proof.** Compactness makes $d$ uniformly continuous. Choose $\delta$ so that $\|d(y)-d(x)\|<\varepsilon/2$ whenever both points lie in the interval and $|y-x|<\delta$. Fix admissible $x,t$ and put $H(y)=f(y)-y\,d(x)$. On the segment from $x$ to $t$, $H'(y)=d(y)-d(x)$ has norm at most $\varepsilon/2$. The norm form of the mean value inequality gives

$$
\|f(t)-f(x)-(t-x)d(x)\|\le(\varepsilon/2)|t-x|.
$$

Divide by $|t-x|>0$. The estimate is uniform in both points and does not require a vector mean value equality. Empty or singleton intervals have no admissible pair of distinct points.

**Lean declarations:** `exercise08_uniform_differentiability`, `exercise08_vector_version`.

<a id="r05e09"></a>
### 5.9 — Filling a missing derivative at zero
**Lean source:** [Exercise09.lean](../../Math/Rudin/Chapter05/Exercise09.lean).
**Inventory status:** Verified as stated.
**Statement.** If $f:\mathbb R\to\mathbb R$ is continuous, differentiable at every nonzero point, and $f'(x)\to3$ as $x\to0$, then $f'(0)$ exists and equals $3$.

**Proof.** For $h\ne0$, apply the mean value theorem on the interval with endpoints $0,h$. There is $c_h$ strictly between them such that $(f(h)-f(0))/h=f'(c_h)$. Since $0<|c_h|<|h|$, the right and left difference quotients both tend to $3$. Equivalently, the one-sided derivative-limit theorem supplies derivatives $3$ on both half-lines, which combine into the ordinary derivative at zero.

**Lean declarations:** `exercise09_derivative_at_zero`.

<a id="r05e10"></a>
### 5.10 — Complex quotients at a one-sided endpoint
**Lean source:** [Exercise10.lean](../../Math/Rudin/Chapter05/Exercise10.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $f,g:(0,1)\to\mathbb C$ be differentiable with respect to the real variable. Suppose, as $x\to0^+$,

$$
f(x),g(x)\to0,\qquad f'(x)\to A,\qquad g'(x)\to B\ne0.
$$

Then $g$ is nonzero for all sufficiently small positive $x$, and $f(x)/g(x)\to A/B$. The separate finite derivative limits distinguish this assertion from Example 5.18.

**Proof.** Extend each function by value zero at zero. The endpoint derivative-limit theorem for normed-space-valued functions gives right derivatives $A$ and $B$. Hence $f(x)/x\to A$ and $g(x)/x\to B$. The second expression is eventually nonzero, so quotient convergence gives the result.

For the comparison, the denominator in Example 5.18 is

$$
G(x)=x+x^2e^{i/x^2},\qquad G'(x)=1+(2x-2i/x)e^{i/x^2}\quad(x\ne0).
$$

For $x>0$, the reverse triangle inequality and $|e^{i/x^2}|=1$ give

$$
|G'(x)|\ge\frac2x-2x-1\longrightarrow\infty.
$$

Thus $G'$ has no finite right-hand limit. Convergence of a quotient of derivatives alone, as in that example, is not the separate derivative-limit hypothesis used here.

**Lean declarations:** `exercise10_endpoint_quotient`, `exercise10_comparison`.

<a id="r05e11"></a>
### 5.11 — Symmetric second differences and a failed converse
**Lean source:** [Exercise11.lean](../../Math/Rudin/Chapter05/Exercise11.lean).
**Inventory status:** Verified as stated.
**Statement.** Suppose $f$ has a first derivative throughout a neighborhood of $x$, and $f''(x)=D$ exists. Then

$$
\lim_{h\to0}\frac{f(x+h)+f(x-h)-2f(x)}{h^2}=D.
$$

A finite symmetric-difference limit does not imply existence of $f''(x)$, even when $f$ is differentiable everywhere.

**Proof.** Put $d=f'$. Differentiability of $d$ at $x$ gives

$$
\frac{d(x+h)-d(x-h)}{2h}\longrightarrow D.
$$

The numerator of the claimed quotient tends to zero by continuity of $f$ at $x$, and its derivative with respect to $h$ is $d(x+h)-d(x-h)$. The denominator tends to zero and has nonzero derivative $2h$ off zero. The real two-sided form of l'Hôpital's rule therefore gives the limit $D$.

For the converse take $f(t)=t|t|$ and $x=0$. Direct differentiation, including the difference quotient at zero, gives $f'(t)=2|t|$. This is not differentiable at zero, since its left and right derivatives are $-2$ and $2$. But $f$ is odd, so $f(h)+f(-h)-2f(0)=0$ for every $h$; the symmetric quotient has limit zero.

**Lean declarations:** `exercise11_second_difference`, `exercise11_converse_counterexample`.

<a id="r05e12"></a>
### 5.12 — Two derivatives of the absolute-value cube
**Lean source:** [Exercise12.lean](../../Math/Rudin/Chapter05/Exercise12.lean).
**Inventory status:** Verified as stated.
**Statement.** For $f(x)=|x|^3$ on $\mathbb R$,

$$
f'(x)=3|x|x,\qquad f''(x)=6|x|
$$

at every real $x$, but $f'''(0)$ does not exist.

**Proof.** On each open half-line, differentiate $x^3$ or $-x^3$. At zero, $|h|^3/h\to0$, which gives the stated first derivative. The difference quotient of $3|x|x$ at zero is $3|h|\to0$, so the second derivative also exists there and has value zero. Finally, the difference quotient of $6|x|$ at zero is $6$ for positive increments and $-6$ for negative increments. Thus the third derivative fails at zero.

**Lean declarations:** `exercise12_first_derivative`, `exercise12_second_derivative`, `exercise12_third_derivative_failure`.

<a id="r05e13"></a>
### 5.13 — Sharp regularity thresholds for a corrected oscillatory function
**Lean source:** [Exercise13.lean](../../Math/Rudin/Chapter05/Exercise13.lean).
**Inventory status:** Verified refutation and correction.
**Statement.** Let $a\in\mathbb R$ and $c>0$. For the explicitly corrected function

$$
F(0)=0,\qquad F(x)=|x|^a\sin(|x|^{-c})\quad(0<|x|\le1),
$$

the seven sharp conclusions are:

1. **(a)** $F$ is continuous on $[-1,1]$ if and only if $a>0$.
2. **(b)** $F'(0)$ exists if and only if $a>1$; then $F'(0)=0$.
3. **(c)** $F'$ exists everywhere on $[-1,1]$ and is bounded if and only if $a\ge1+c$.
4. **(d)** $F'$ exists everywhere and is continuous if and only if $a>1+c$.
5. **(e)** $F''(0)$ exists, with a genuine first derivative near zero, if and only if $a>2+c$; then $F''(0)=0$. Requiring the first derivative on the entire interval is equivalent here.
6. **(f)** Both derivatives exist everywhere and $F''$ is bounded if and only if $a\ge2+2c$.
7. **(g)** Both derivatives exist everywhere and $F''$ is continuous if and only if $a>2+2c$.

All interval derivatives include one-sided derivatives at $-1$ and $1$. At $a=1+c$, the first derivative is bounded but not continuous. At $a=2+2c$, the second derivative is bounded but not continuous.

**Correction.** The printed prefactor is $x^a$, not $|x|^a$. For arbitrary real $a$, it is not a real-valued expression at negative $x$: $a=1/2$, $x=-1$ would require a real $y$ with $y^2=-1$, impossible because $y^2\ge0$. The seven results above concern a selected absolute-power correction, not a proof of the printed formula or an OCR repair.

**Proof.** Away from zero the corrected function is smooth. For $t>0$, define

$$
\begin{aligned}
Q(t)&=a t^{a-1}\sin(t^{-c})-c t^{a-c-1}\cos(t^{-c}),\\
R(t)&=a(a-1)t^{a-2}\sin(t^{-c})
-c(2a-c-1)t^{a-c-2}\cos(t^{-c})
-c^2t^{a-2c-2}\sin(t^{-c}).
\end{aligned}
$$

The product and chain rules give, for $x\ne0$,

$$
F'(x)=\operatorname{sgn}(x)Q(|x|),\qquad F''(x)=R(|x|).
$$

These formulas apply on both half-lines and give the required endpoint derivatives. Whenever the derivatives exist at zero, extend these displayed functions by value zero there.

For the sufficient conditions, use $|\sin|,|\cos|\le1$. First,

$$
|F(x)|\le |x|^a,\qquad |F(x)/x|\le |x|^{a-1}.
$$

These bounds prove (a) for $a>0$ and (b) for $a>1$. The first-derivative bound is

$$
|F'(x)|\le |a||x|^{a-1}+c|x|^{a-c-1}.
$$

Nonnegative exponents give boundedness on $0<|x|\le1$; strictly positive exponents give convergence to zero. Since $c>0$, this proves the sufficient conditions in (c) and (d), including derivative existence at zero. Similarly,

$$
|F'(x)/x|\le |a||x|^{a-2}+c|x|^{a-c-2},
$$

which gives $F''(0)=0$ when $a>2+c$. Finally, bounding the three terms of $R$ gives boundedness when $a\ge2+2c$ and convergence to zero when $a>2+2c$. These thresholds also ensure that the lower derivatives exist.

For necessity, use the positive sequences

$$
t_n(b)=(b+2\pi(n+1))^{-1/c}\longrightarrow0,
$$

where $b=0,\pi,\pi/2$. They eventually lie in $(0,1]$ and satisfy $\sin(t_n(b)^{-c})=\sin b$ and $\cos(t_n(b)^{-c})=\cos b$.

At $b=\pi/2$, $F(t_n)=t_n^a$. Continuity at zero therefore forces $a>0$. Since $F$ is even, any derivative at zero must be zero. The same samples give $F(t_n)/t_n=t_n^{a-1}$, forcing $a>1$.

At $b=0$, $Q(t_n)=-c\,t_n^{a-c-1}$. Boundedness of the first derivative forces $a-c-1\ge0$; continuity at its zero value forces $a-c-1>0$. For the second derivative at zero, the first derivative is necessarily the displayed function wherever it exists. Its difference quotients on phases $b=0$ and $b=\pi$ are respectively

$$
-c\,t_n(0)^{a-c-2},\qquad c\,t_n(\pi)^{a-c-2}.
$$

A negative exponent is unbounded. At exponent zero the two limits are $-c$ and $c$, which differ. Thus a second derivative requires $a>2+c$. Off-zero smoothness shows that a local first derivative near zero can be extended to the whole interval, so the local and interval formulations agree.

For $R$, the sine-one samples give

$$
R(t_n(\pi/2))=t_n(\pi/2)^{a-2c-2}
\bigl(a(a-1)t_n(\pi/2)^{2c}-c^2\bigr).
$$

The factor in parentheses tends to $-c^2\ne0$. Boundedness forces the exponent to be nonnegative; convergence to $F''(0)=0$ forces it to be positive. This proves (f) and (g). The same samples show discontinuity at each equality threshold, while the preceding bounds prove boundedness there.

**Lean declarations:** `exercise13_a`, `exercise13_b`, `exercise13_c`, `exercise13_first_equality`, `exercise13_d`, `exercise13_e`, `exercise13_e_local`, `exercise13_e_local_iff_interval`, `exercise13_f`, `exercise13_second_equality`, `exercise13_g`, `exercise13_domain_obstruction`.

<a id="r05e14"></a>
### 5.14 — Derivative criteria for convexity
**Lean source:** [Exercise14.lean](../../Math/Rudin/Chapter05/Exercise14.lean).
**Inventory status:** Verified as stated.
**Statement.** For a real function differentiable on $(a,b)$, convexity is equivalent to $f'$ being nondecreasing there. If $f'$ is also differentiable throughout $(a,b)$, convexity is equivalent to $f''(x)\ge0$ for every $x\in(a,b)$. No continuity of $f'$ or $f''$ is added.

**Proof.** For a differentiable convex function, the secant-slope inequalities give

$$
f'(x)\le\frac{f(y)-f(x)}{y-x}\le f'(y)\qquad(x<y).
$$

Thus $f'$ is nondecreasing. Conversely, the mean value theorem and monotonicity of $f'$ order the slopes on successive subintervals; those slope inequalities are the convexity inequality. This is the standard derivative criterion for convexity used in the source. Applying the derivative test for monotonicity to $f'$ gives the second assertion: a differentiable nondecreasing function has nonnegative derivative, and a nonnegative derivative implies nondecrease by the mean value theorem. Empty intervals cause no exception.

**Lean declarations:** `exercise14_first_derivative_criterion`, `exercise14_second_derivative_criterion`.

<a id="r05e15"></a>
### 5.15 — A sharp bound for the first derivative
**Lean source:** [Exercise15.lean](../../Math/Rudin/Chapter05/Exercise15.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $f$ have two genuine derivatives on $(a,\infty)$. If $M_0,M_2$ are finite bounds for $|f|,|f''|$, then $|f'|$ has a finite supremum $M_1$ and

$$
M_1^2\le4M_0M_2.
$$

In particular this holds when the three $M_j$ are finite least upper bounds of $|f^{(j)}|$. Either $M_0=0$ or $M_2=0$ forces $f'=0$. The constant $4$ is sharp. All these assertions also hold in Euclidean norm for vector-valued functions, and indeed in any real normed space.

**Scope.** The numerical assertion uses finite real bounds or finite real suprema. It does not assign extended-real values to products involving infinite suprema. Continuity of the second derivative is not required.

**Proof.** The norm Taylor inequality of Exercise 5.20 on $[x,x+2h]$, for $h>0$, yields

$$
\|f(x+2h)-f(x)-2hf'(x)\|\le2h^2M_2.
$$

The triangle inequality therefore gives

$$
2h\|f'(x)\|\le2M_0+2h^2M_2.
$$

Write $u=\|f'(x)\|$. If $M_2>0$ and $u>0$, substitute $h=u/(2M_2)$ to obtain $u^2\le4M_0M_2$. The case $u=0$ is immediate. If $M_2=0$ and $u>0$, choosing $h>(M_0/u)$ contradicts the displayed inequality. Thus the pointwise bound holds in every case. It bounds $\|f'\|$ by $\sqrt{4M_0M_2}$, proves existence of its finite supremum, and passes to that supremum. It also handles either zero bound.

For sharpness on $(-1,\infty)$, take

$$
f(x)=\begin{cases}2x^2-1,&-1<x<0,\\(x^2-1)/(x^2+1),&x\ge0.\end{cases}
$$

Its derivatives are

$$
f'(x)=\begin{cases}4x,&x<0,\\4x/(x^2+1)^2,&x\ge0,\end{cases}\qquad
f''(x)=\begin{cases}4,&x<0,\\4(1-3x^2)/(x^2+1)^3,&x\ge0.\end{cases}
$$

The two pieces of $f$ agree at zero with value $-1$; their first derivatives agree with value $0$, and their second derivatives agree with value $4$. The one-sided derivatives therefore combine to give both genuine derivatives at the join.

On $(-1,0)$ the bounds $|f|\le1$, $|f'|\le4$, and $|f''|\le4$ follow directly. For $x\ge0$, $|x^2-1|\le x^2+1$, $x\le(1+x^2)^2$, and $|1-3x^2|\le(1+x^2)^3$ give the same bounds. Here the middle inequality follows from $1+x^2-x>0$, and the last follows by expanding both inequalities with $u=x^2\ge0$. The value at zero gives $M_0=1$ and $M_2=4$; as $x\to-1^+$, $|f'(x)|\to4$, so $M_1=4$. Consequently $M_1^2=16=4M_0M_2$.

**Lean declarations:** `exercise15_derivative_bound`, `exercise15_finite_supremum`, `exercise15_zero_bound`, `exercise15_example_regular`, `exercise15_example_function_supremum`, `exercise15_example_derivative_supremum`, `exercise15_example_second_derivative_supremum`, `exercise15_example_sharpness`, `exercise15_vector_version`.

<a id="r05e16"></a>
### 5.16 — A bounded second derivative controls the limiting first derivative
**Lean source:** [Exercise16.lean](../../Math/Rudin/Chapter05/Exercise16.lean).
**Inventory status:** Verified as stated.
**Statement.** Suppose $f$ has two derivatives on $(0,\infty)$, $f''$ is bounded there, and $f(x)\to0$ as $x\to\infty$. Then $f'(x)\to0$. The source proves this in any real normed space, in particular for real functions.

**Proof.** Choose $B\ge0$ with $\|f''(t)\|\le B$. Given $\varepsilon>0$, put $\eta=\varepsilon^2/(8(B+1))$. On a sufficiently late half-line, $\|f(t)\|\le\eta$. Apply the pointwise bound of Exercise 5.15 on that half-line:

$$
\|f'(x)\|^2\le4\eta B<\varepsilon^2.
$$

Thus $\|f'(x)\|<\varepsilon$ for all sufficiently large $x$. This proof also covers $B=0$ and assumes no continuity of $f''$.

**Lean declarations:** `exercise16_derivative_limit`.

<a id="r05e17"></a>
### 5.17 — A sharp third-derivative bound
**Lean source:** [Exercise17.lean](../../Math/Rudin/Chapter05/Exercise17.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $f$ have three derivatives within $[-1,1]$, with

$$
f(-1)=f(0)=f'(0)=0,\qquad f(1)=1.
$$

There is $x\in(-1,1)$ with $f'''(x)\ge3$. In fact, the source proves $f'''(x)=3$ at some such point. The bound is sharp.

**Proof.** Let $p(t)=(t^3+t^2)/2$ and $g=f-p$. Then $g(-1)=g(0)=g(1)=g'(0)=0$. Rolle's theorem produces zeros of $g'$ at $u\in(-1,0)$ and $v\in(0,1)$. Applying it to $g'$ on $[u,0]$ and $[0,v]$ gives zeros of $g''$ at $s<0<t$. Applying it to $g''$ on $[s,t]$ gives $g'''(x)=0$ somewhere inside. Since $p'''=3$, this means $f'''(x)=3$. The polynomial $p$ itself satisfies all four data and has third derivative identically $3$, so no larger universal lower bound is possible. Endpoint derivatives used here are only within the interval.

**Lean declarations:** `exercise17_third_derivative_lower_bound`, `exercise17_third_derivative_eq`, `exercise17_sharpness`.

<a id="r05e18"></a>
### 5.18 — An exact Taylor identity from a quotient
**Lean source:** [Exercise18.lean](../../Math/Rudin/Chapter05/Exercise18.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $n\ge1$ be an integer. Suppose $f$ has genuine derivatives through order $n-1$ on $[a,b]$, with one-sided derivatives at endpoints. For distinct $\alpha,\beta\in[a,b]$, define

$$
P(t)=\sum_{k=0}^{n-1}\frac{f^{(k)}(\alpha)}{k!}(t-\alpha)^k,
\qquad Q(t)=\frac{f(t)-f(\beta)}{t-\beta}\quad(t\ne\beta).
$$

Then $Q$ has derivatives through order $n-1$ on $[a,b]\setminus\{\beta\}$, and

$$
f(\beta)=P(\beta)+\frac{Q^{(n-1)}(\alpha)}{(n-1)!}(\beta-\alpha)^n.
$$

**Proof.** The quotient rule first constructs $Q'$ wherever $t\ne\beta$. Repeated differentiation of $(t-\beta)Q(t)=f(t)-f(\beta)$ gives, for $1\le k\le n-1$,

$$
f^{(k)}(t)=(t-\beta)Q^{(k)}(t)+kQ^{(k-1)}(t).
$$

Equivalently, $Q^{(k)}=(f^{(k)}-kQ^{(k-1)})/(t-\beta)$; induction with the quotient rule proves these are genuine derivatives, including within derivatives at retained endpoints. Substituting $t=\alpha$ into these identities and successively eliminating $Q(\alpha),\ldots,Q^{(n-2)}(\alpha)$ gives the displayed formula. More explicitly, the identity for order $m+1$ follows from that for order $m$ by this recurrence and $(m+1)!= (m+1)m!$. At $n=1$ there is no derivative hypothesis: the formula is simply $f(\beta)=f(\alpha)+Q(\alpha)(\beta-\alpha)$.

**Lean declarations:** `exercise18_quotient_taylor_identity`.

<a id="r05e19"></a>
### 5.19 — Secants whose endpoints approach zero
**Lean source:** [Exercise19.lean](../../Math/Rudin/Chapter05/Exercise19.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $f:(-1,1)\to\mathbb R$ have derivative $L=f'(0)$. Suppose $-1<\alpha_n<\beta_n<1$ and both sequences tend to zero. Set

$$
D_n=\frac{f(\beta_n)-f(\alpha_n)}{\beta_n-\alpha_n}.
$$

Then $D_n\to L$ under each of these sufficient conditions:

1. **(a)** $\alpha_n<0<\beta_n$ for all $n$.
2. **(b)** $0<\alpha_n<\beta_n$ and $\beta_n/(\beta_n-\alpha_n)$ is bounded.
3. **(c)** $f$ is differentiable throughout $(-1,1)$ and $f'$ is continuous there. Continuity of $f'$ at zero alone also suffices.

Without these additional conditions, there is an everywhere differentiable example for which $D_n$ has a finite limit different from $f'(0)$.

**Proof.** For $t\ne0$, put $r(t)=(f(t)-f(0))/t-L$, so $r(t)\to0$. When the endpoints are nonzero,

$$
D_n-L=\frac{\beta_n}{\beta_n-\alpha_n}r(\beta_n)
-\frac{\alpha_n}{\beta_n-\alpha_n}r(\alpha_n).
$$

In (a), the first coefficient lies between zero and one, and the absolute value of the second does too. In (b), the first coefficient is bounded by assumption, and the second equals the first minus one. Thus both terms tend to zero in each case. In (c), the mean value theorem gives $D_n=f'(c_n)$ with $\alpha_n<c_n<\beta_n$. Hence $c_n\to0$, and continuity of $f'$ at zero finishes the proof.

For the counterexample take $f(0)=0$ and $f(x)=x^2\sin(1/x)$ for $x\ne0$. The bound $|f(x)/x|\le|x|$ gives $f'(0)=0$, and the function is differentiable away from zero. Set

$$
p_n=2\pi(n+1),\qquad \alpha_n=\frac1{p_n+\pi/2},\qquad \beta_n=\frac1{p_n}.
$$

These satisfy $0<\alpha_n<\beta_n<1$ and tend to zero. Since $f(\beta_n)=0$ and $f(\alpha_n)=\alpha_n^2$,

$$
D_n=-\frac{1-(\pi/2)\alpha_n}{\pi/2}\longrightarrow-\frac2\pi\ne0.
$$

The derivative cannot be continuous at zero, since (c) would then force the same secants to tend to zero.

**Lean declarations:** `exercise19_a`, `exercise19_b`, `exercise19_c`, `exercise19_different_limit`.

<a id="r05e20"></a>
### 5.20 — Taylor's inequality for vector-valued functions
**Lean source:** [Exercise20.lean](../../Math/Rudin/Chapter05/Exercise20.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $E$ be a real normed space, $n\ge0$ an integer, and $I$ the closed interval with endpoints $a,b$ in either order. Suppose functions $F_0,\ldots,F_n:I\to E$ satisfy $F_k'=F_{k+1}$ within $I$ for $k<n$, and $\|F_n(t)\|\le M$ on $I$. Then

$$
\left\|F_0(b)-\sum_{k=0}^{n-1}\frac{(b-a)^k}{k!}F_k(a)\right\|
\le\frac{M|b-a|^n}{n!}.
$$

This includes Euclidean vector-valued functions, both directions, one-sided endpoint derivatives, and $n=0$ with an empty sum. The highest derivative need not be continuous.

**Proof.** First work on $[0,1]$ and prove the corresponding bound at every $t$ by induction on $n$. For $n=0$ it is the given bound. For the induction step, subtract the Taylor polynomial of order $n$ and call the remainder $R$. Its derivative is the order-$n$ remainder for the derivative sequence $F_1,F_2,\ldots$. The induction hypothesis gives

$$
\|R'(t)\|\le M t^n/n!.
$$

Also $R(0)=0$. The norm derivative comparison theorem, applied against the scalar function $B(t)=Mt^{n+1}/(n+1)!$, whose derivative is the right-hand bound, gives $\|R(t)\|\le B(t)$. This theorem is the norm mean value inequality with a differentiable scalar majorant, so it needs no continuity of $F_{n+1}$.

For general endpoints put $d=b-a$ and $G_k(t)=d^kF_k(a+td)$ on $[0,1]$. The chain rule gives $G_k'=G_{k+1}$, and $\|G_n\|\le|d|^nM$. The unit-interval result at $t=1$ is exactly the displayed estimate. This change of variables also works for $d<0$ and $d=0$; at $n=0$ the convention is $|d|^0=1$.

**Lean declarations:** `exercise20_vector_taylor_bound`.

<a id="r05e21"></a>
### 5.21 — Closed sets as smooth zero sets
**Lean source:** [Exercise21.lean](../../Math/Rudin/Chapter05/Exercise21.lean).
**Inventory status:** Verified as stated.
**Statement.** Every closed set $E\subset\mathbb R$ is exactly the zero set of a smooth real function on $\mathbb R$. Thus it is the zero set of a differentiable function and, for every positive integer $n$, of an $n$-times-differentiable function. The construction includes $E=\varnothing$ and $E=\mathbb R$.

**Proof.** Apply the smooth separation theorem for disjoint closed sets, obtained by partitions of unity, to $E$ and the empty set. The theorem supplies a smooth function $f$ with $f(x)=0$ exactly when $x\in E$ (and the second prescribed level set empty). This is the library theorem used in the source. Smoothness implies that every iterated derivative exists and is differentiable; retaining only the first $n$ derivative steps gives the finite-order assertion, and retaining the first gives the differentiable assertion. For the boundary cases one can also take $f=1/2$ when $E=\varnothing$ and $f=0$ when $E=\mathbb R$. The finite-order result in the file permits $n=0$ as well, with no derivative steps required.

**Lean declarations:** `exercise21_differentiable_zero_set`, `exercise21_finite_order_zero_set`, `exercise21_smooth_zero_set`.

<a id="r05e22"></a>
### 5.22 — Fixed points, contractions, and iteration paths
**Lean source:** [Exercise22.lean](../../Math/Rudin/Chapter05/Exercise22.lean).
**Inventory status:** Verified as stated.
**Statement.** The following assertions concern real functions on $\mathbb R$.

1. **(a)** If $f$ is differentiable and $f'(t)\ne1$ everywhere, it has at most one fixed point.
2. **(b)** The function $f(t)=t+1/(1+e^t)$ has no fixed point, although $0<f'(t)<1$ everywhere.
3. **(c)** If $f$ is differentiable and $|f'(t)|\le A<1$ everywhere, it has exactly one fixed point $z$. For every starting value $x_1$, the iteration $x_{n+1}=f(x_n)$ converges to $z$.
4. **(d)** The graph/diagonal iteration path has successive vertices $(x_n,x_{n+1})$, $(x_{n+1},x_{n+1})$, $(x_{n+1},x_{n+2})$.

**Proof.** If two distinct fixed points existed in (a), the mean value theorem between them would give $f'(c)=1$, a contradiction. In (b), the displacement $1/(1+e^t)$ is strictly positive, so there is no fixed point. Differentiation gives

$$
f'(t)=1-\frac{e^t}{(1+e^t)^2}.
$$

For $u=e^t>0$, $0<u/(1+u)^2<1$, proving the derivative inequalities.

In (c), the derivative bound forces $A\ge0$, and the mean value theorem gives $|f(x)-f(y)|\le A|x-y|$. The contraction mapping theorem on the complete space $\mathbb R$ supplies a unique fixed point and convergence of every orbit to it. Unlike (b), this uses one uniform constant strictly below one; $A=0$ is included.

For (d), $x_{n+1}=f(x_n)$ puts the first vertex on the graph. Holding its second coordinate fixed gives the horizontal segment to the diagonal; holding the new first coordinate fixed gives the vertical segment back to the graph:

```mermaid
flowchart LR
    G["(x_n, x_(n+1)): graph"] -->|horizontal| D["(x_(n+1), x_(n+1)): diagonal"]
    D -->|vertical| H["(x_(n+1), x_(n+2)): graph"]
```

The horizontal segment consists exactly of points $(s,x_{n+1})$ with $s$ between $x_n$ and $x_{n+1}$. The vertical segment consists exactly of $(x_{n+1},s)$ with $s$ between $x_{n+1}$ and $x_{n+2}$. These descriptions include degenerate segments at fixed points.

**Lean declarations:** `exercise22_a`, `exercise22_b_no_fixed_point`, `exercise22_b_hasDerivAt`, `exercise22_b_derivative`, `exercise22_c_existence`, `exercise22_c_iteration`, `exercise22_d_segments`, `exercise22_d_vertices`.

<a id="r05e23"></a>
### 5.23 — Complete iteration regions for a cubic map
**Lean source:** [Exercise23.lean](../../Math/Rudin/Chapter05/Exercise23.lean).
**Inventory status:** Verified as stated.
**Statement.** For $f(x)=(x^3+1)/3$, there are exactly three fixed points,

$$
\alpha\in(-2,-1),\qquad\beta\in(0,1),\qquad\gamma\in(1,2).
$$

For $x_{n+1}=f(x_n)$ the exact limit regions are

$$
\begin{aligned}
x_n\to-\infty&\quad\Longleftrightarrow\quad x_1<\alpha,\\
x_n\to\beta&\quad\Longleftrightarrow\quad\alpha<x_1<\gamma,\\
x_n\to+\infty&\quad\Longleftrightarrow\quad\gamma<x_1.
\end{aligned}
$$

Starting at any fixed point gives a constant sequence.

**Proof.** The polynomial $p(x)=x^3-3x+1$ has opposite signs at the endpoints of each of $[-2,-1]$, $[0,1]$, and $[1,2]$. The intermediate value theorem gives three roots in the stated open intervals. Since these are distinct, the monic cubic factors as

$$
f(x)-x=\frac{(x-\alpha)(x-\beta)(x-\gamma)}3,
$$

so there are no other fixed points. The map $f$ is strictly increasing. The factorization shows $f(x)<x$ below $\alpha$, $f(x)>x$ between $\alpha$ and $\beta$, $f(x)<x$ between $\beta$ and $\gamma$, and $f(x)>x$ above $\gamma$.

A start below $\alpha$ therefore gives a decreasing orbit. If bounded below, it would converge to a finite limit $l\le x_1<\alpha$; continuity would make $l$ a fixed point, impossible. Hence it tends to $-\infty$. The argument above $\gamma$ is the increasing counterpart. Between $\alpha$ and $\beta$, monotonicity of $f$ keeps the orbit below $\beta$, while the sign rule makes it increase. Its limit is a fixed point in $[x_1,\beta]$, necessarily $\beta$. Between $\beta$ and $\gamma$, it decreases to $\beta$ by the same argument. A start at $\beta$ is constant. Finally, monotonicity preserves the bounds by $\alpha$ and $\gamma$ for starts outside the middle region; these bounds exclude the other limits and prove all three converses. Starts at $\alpha$ and $\gamma$ remain at those values.

**Lean declarations:** `exercise23_roots_exist`, `exercise23_fixed_points`, `exercise23_classification`, `exercise23_a`, `exercise23_exact_regions`, `exercise23_b`, `exercise23_c`.

<a id="r05e24"></a>
### 5.24 — Quadratic and linear square-root iterations
**Lean source:** [Exercise24.lean](../../Math/Rudin/Chapter05/Exercise24.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $\alpha>0$, $\alpha\ne1$, and $r=\sqrt\alpha$. On the positive half-line consider

$$
N(x)=\frac{x+\alpha/x}{2},\qquad H(x)=\frac{\alpha+x}{1+x}.
$$

Both maps have the unique positive fixed point $r$, and both iterations converge to $r$ from every positive start. A start at $r$ is constant. For any other positive start, the Newton iteration $u_{n+1}=N(u_n)$ has rates

$$
\frac{u_{n+1}-r}{(u_n-r)^2}\to\frac1{2r},\qquad
\frac{u_{n+1}-r}{u_n-r}\to0.
$$

The other iteration $v_{n+1}=H(v_n)$ has signed linear rate

$$
\frac{v_{n+1}-r}{v_n-r}\to q=\frac{1-r}{1+r},\qquad
\frac{|v_{n+1}-r|}{|v_n-r|}\to|q|,\qquad0<|q|<1.
$$

For $\alpha>1$ this second iteration alternates about $r$; for $0<\alpha<1$ it approaches $r$ monotonically from the starting side. These rates explain the different speeds in Chapter 3, Exercises 16 and 17.

**Proof.** All denominators are positive on the stated domain, and both maps preserve positivity. Each fixed-point equation reduces to $x^2=\alpha$, so its unique positive solution is $r$. Differentiation gives

$$
N'(x)=\frac{1-\alpha/x^2}{2},\qquad H'(x)=\frac{1-\alpha}{(1+x)^2},\qquad N'(r)=0,\quad H'(r)=q.
$$

More precisely, direct algebra gives

$$
N(x)-r=\frac{(x-r)^2}{2x},\qquad
H(x)-r=\frac{(1-r)(x-r)}{1+x}.
$$

For a nonfixed Newton start, the first iterate is strictly above $r$. Above $r$, $r<N(x)<x$, so the subsequent orbit decreases to a limit at least $r$. Continuity and the unique positive fixed point identify the limit as $r$. The exact error identity shows that the orbit never reaches $r$, and division by its nonzero errors gives the two stated rates.

For the other map, define $z_n=(v_n-r)/(v_n+r)$. Its exact recurrence is $z_{n+1}=qz_n$, hence

$$
z_n=q^{n-1}\frac{v_1-r}{v_1+r}.
$$

Since $r>0$, $|q|<1$, so $z_n\to0$ and $v_n=r(1+z_n)/(1-z_n)\to r$. Since $\alpha\ne1$, $q\ne0$; a nonfixed orbit never reaches $r$. Divide the second error identity by $v_n-r$ and take limits to obtain the signed rate, then take absolute values.

The complete graph/diagonal paths use the horizontal and vertical segments of Exercise 5.22 for either orbit. For Newton, a start above $r$ decreases strictly and stays above it. A start below $r$ moves above $r$ in one step, then decreases strictly. For $\alpha>1$, $-1<q<0$, so the $H$-orbit changes side at every step. Its terms on the upper side decrease strictly and those on the lower side increase strictly. Indeed,

$$
H(H(y))-y=\frac{2(\alpha-y^2)}{\alpha+1+2y},
$$

which has the required sign on each side. If the start is above $r$, the odd-numbered terms are above and decrease, while the even-numbered terms are below and increase; for a start below $r$ the roles reverse. For $0<\alpha<1$, $0<q<1$ and the error identity preserves sides. Also $H(y)-y=(\alpha-y^2)/(1+y)$, so each step moves strictly toward $r$ without crossing it. A root start gives degenerate segments.

```mermaid
flowchart LR
    A["(w_n, w_(n+1)) on graph of N or H"] -->|horizontal| B["(w_(n+1), w_(n+1)) on diagonal"]
    B -->|vertical| C["(w_(n+1), w_(n+2)) on the same graph"]
```

Here the horizontal coordinate ranges between $w_n,w_{n+1}$ on the first segment, and the vertical coordinate ranges between $w_{n+1},w_{n+2}$ on the second. Alternation describes scalar iterates on opposite sides of $r$, not a claim that a planar segment passes through $(r,r)$.

**Lean declarations:** `exercise24_fixed_points`, `exercise24_constant`, `exercise24_derivatives_at_root`, `exercise24_newton_convergence`, `exercise24_newton_rates`, `exercise24_mobius_convergence`, `exercise24_mobius_rates`, `exercise24_rate_signs`, `exercise24_newton_diagrams`, `exercise24_greater_than_one_diagrams`, `exercise24_diagram_segments`, `exercise24_less_than_one_diagrams`.

<a id="r05e25"></a>
### 5.25 — Newton iteration with termination and zero-curvature corrections
**Lean source:** [Exercise25.lean](../../Math/Rudin/Chapter05/Exercise25.lean).
**Inventory status:** Verified refutation and correction.
**Statement.** Let $a<b$ and let $f$ have genuine first and second derivatives $p=f'$ and $q=f''$ within $[a,b]$. Suppose

$$
f(a)<0<f(b),\qquad p(x)\ge\delta>0,\qquad0\le q(x)\le M\quad(x\in[a,b]).
$$

There is a unique zero $\xi\in(a,b)$. Start with $\xi<x_1\le b$ and define the infinite Newton sequence

$$
x_{n+1}=g(x_n),\qquad g(x)=x-\frac{f(x)}{p(x)}.
$$

The results, with the corrected termination convention, are:

1. **(a)** Every iterate lies in $[\xi,b]$ and has positive derivative denominator. The next term is the unique horizontal-axis intercept of the tangent at $(x_n,f(x_n))$. Once the root is reached, all later terms equal it.
2. **(b)** $\xi\le x_{n+1}\le x_n$, with $x_{n+1}<x_n$ if and only if $x_n>\xi$, and $x_n\to\xi$.
3. **(c)** If $x_n>\xi$, there is $t_n\in(\xi,x_n)$ such that

   $$
   x_{n+1}-\xi=\frac{q(t_n)}{2p(x_n)}(x_n-\xi)^2.
   $$

   If $x_n=\xi$, the next error is zero and no point of $(\xi,x_n)$ exists.
4. **(d)** Put $A=M/(2\delta)\ge0$ and $e_n=x_n-\xi$. Then

   $$
   0\le e_{n+1}\le Ae_n^2,\qquad
      0\le e_{n+1}\le A^{2^n-1}e_1^{2^n}\quad(n\ge0).
   $$

   The second formula at $n=0$ is $e_1\le e_1$, using the usual zeroth-power convention. If $A>0$, it also reads $e_{n+1}\le(Ae_1)^{2^n}/A$. If $A=0$, equivalently $M=0$, then $x_n=\xi$ for all $n\ge2$.
5. **(e)** Fixed points of $g$ on $[a,b]$ are exactly zeros of $f$. Within this interval,

   $$
   g'(x)=\frac{f(x)q(x)}{p(x)^2}.
   $$

   At the interior root $g'(\xi)=0$, and the actual derivative satisfies $g'(x)\to0$ as $x\to\xi$, without continuity of $q$.
6. **(f)** For the signed real cube-root function $h(x)=\sqrt[3]{x}$, Newton iteration from a nonzero start is $x_n=(-2)^{n-1}x_1$. Every step is defined, signs alternate, and $|x_n|\to\infty$. The function $h$ is not differentiable at zero.

**Correction.** The source requires $x_1<b$; the verified proof also permits $x_1=b$ using one-sided endpoint derivatives. The printed all-step strict descent and interior Taylor-point claims are false after finite termination. On $[-1,1]$, take $f(x)=x$, $\delta=1$, $M=1$, and $x_1=1/2$. Then $\xi=0$ and $x_2=x_3=\cdots=0$. Thus later steps are not strict and the Taylor interval is empty. This termination defect does not require a zero upper bound: the counterexample above uses $M=1$. The same affine function also permits $M=0$, when $A=0$ and the printed $1/A$ is undefined. There is no real number $r$ with $0r=1$. The denominator-free bound above is the correction; strict convexity is not added.

**Proof.** Continuity and the endpoint signs give a zero by the intermediate value theorem. Since $p\ge\delta>0$, the mean value theorem makes $f$ strictly increasing, so the zero is unique and interior. Existence of the second derivative makes $p$ continuous on $[a,b]$; $q\ge0$ also makes $p$ nondecreasing.

For $\xi<x\le b$, Taylor's theorem at $x$, evaluated at $\xi$, gives

$$
0=f(\xi)=f(x)+p(x)(\xi-x)+\tfrac12q(t)(\xi-x)^2
\quad\text{for some }t\in(\xi,x).
$$

This form needs no continuity of $q$. To obtain it by Rolle's theorem, subtract from $f(y)$ its tangent at $x$ and a quadratic $C(y-x)^2$ chosen to make the remainder vanish at $\xi$. It also vanishes at $x$. Rolle first gives a zero of its first derivative between them; that derivative already vanishes at $x$. A second application of Rolle gives $q(t)=2C$. Rearranging yields (c).

The nonnegative Taylor error implies $g(x)\ge\xi$, while $f(x)>0$ and $p(x)>0$ imply $g(x)<x$ off the root. At the root $g(\xi)=\xi$. Induction proves invariance, positive denominators, weak descent, strictness exactly off the root, and absorption after termination. Solving

$$
f(x)+p(x)(y-x)=0
$$

for $y$ gives the unique intercept $y=g(x)$, proving the tangent assertion.

Monotone boundedness gives $x_n\to l\in[\xi,b]$. Since $f,p$ are continuous and $p(l)>0$, passing to the limit in the recurrence gives $l=g(l)$, hence $f(l)=0$ and $l=\xi$.

Use $q(t)\le M$ and $p(x)\ge\delta$ in (c) to obtain $0\le e_{n+1}\le Ae_n^2$; the same inequality holds at a terminated step. Induction gives the denominator-free bound: squaring the bound at exponent $2^n$ and multiplying by $A$ changes the power of $A$ from $2(2^n-1)+1$ to $2^{n+1}-1$. This calculation involves no division by $A$. If $A>0$, algebra gives the printed reciprocal form. If $M=0$, the one-step inequality forces zero error immediately. Positivity of $2\delta$ proves $A=0$ if and only if $M=0$.

The quotient rule gives $g'=fq/p^2$, including within derivatives at endpoints; $g(x)=x$ is equivalent to $f(x)=0$ because $p(x)>0$. Near the root,

$$
|g'(x)|\le |f(x)|\frac{M}{\delta^2}\longrightarrow0.
$$

At $\xi$ the formula gives derivative zero. Since $\xi$ is interior, these are ordinary local derivatives and their ordinary limit.

Finally let $r=h(x)$, so $r^3=x$ for every real $x$. Off zero, inverse differentiation gives $h'(x)=1/(3r^2)\ne0$. Therefore

$$
x-\frac{h(x)}{h'(x)}=x-3r^3=-2x.
$$

Induction yields the stated iterates, none zero, and $|x_n|=2^{n-1}|x_1|\to\infty$. If $h$ were differentiable at zero, differentiation of $h(x)^3=x$ there would give $0=1$. Thus the derivative obstruction is genuine, not an assigned derivative value.

**Lean declarations:** `exercise25_root`, `exercise25_iteration`, `exercise25_iteration_absorbing`, `exercise25_tangent`, `exercise25_strict_step`, `exercise25_termination_counterexample`, `exercise25_convergence`, `exercise25_taylor`, `exercise25_taylor_terminated`, `exercise25_quadratic`, `exercise25_denominator_free`, `exercise25_printed_bound`, `exercise25_fixed_point`, `exercise25_g_derivative`, `exercise25_g_derivative_root`, `exercise25_deriv_limit`, `exercise25_cube_root_derivative`, `exercise25_cube_root_iterates`, `exercise25_cube_root_well_defined`, `exercise25_cube_root_divergence`, `exercise25_cube_root_not_differentiable`, `exercise25_zero_curvature`, `exercise25_A_zero_iff`, `exercise25_zero_A_termination`, `exercise25_zero_bound_domain_obstruction`.

<a id="r05e26"></a>
### 5.26 — A differential inequality with zero initial value
**Lean source:** [Exercise26.lean](../../Math/Rudin/Chapter05/Exercise26.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $f$ have derivative $v$ within $[a,b]$, suppose $f(a)=0$, and assume

$$
|v(x)|\le A|f(x)|\qquad(x\in[a,b])
$$

for a real constant $A$ of any sign. Then $f=0$ throughout $[a,b]$. The source also proves the normed-space version $\|v(x)\|\le A\|f(x)\|$.

**Proof.** Apply the differential form of Grönwall's zero-initial-value theorem: a continuous normed-space-valued function whose right derivative satisfies $\|f'_+(x)\|\le A\|f(x)\|$ and whose initial value is zero vanishes to the right. Within differentiability supplies continuity on $[a,b]$ and the needed right derivative at every $x<b$, so this standard theorem applies directly. This is the library result used in the source; it permits every real $A$. In particular, for $A<0$, the original inequality already forces $f(x)=0$ at each point, and for $A=0$ the derivative vanishes. If $a=b$, the conclusion is just the initial value; if $a>b$, the interval is empty. No ambient endpoint derivatives are needed.

**Lean declarations:** `exercise26_zero_solution`.

<a id="r05e27"></a>
### 5.27 — Scalar differential-equation uniqueness and waiting-time solutions
**Lean source:** [Exercise27.lean](../../Math/Rudin/Chapter05/Exercise27.lean).
**Inventory status:** Verified as stated.
**Statement.** Suppose $\phi$ is real-valued on $[a,b]\times[\alpha,\beta]$ and, for a fixed real $A$,

$$
|\phi(x,u)-\phi(x,v)|\le A|u-v|
$$

for all points of that rectangle with the same $x$. Then two differentiable solutions taking values in $[\alpha,\beta]$ of $y'=\phi(x,y)$ with the same initial value $y(a)=c\in[\alpha,\beta]$ agree on $[a,b]$. The equation and derivatives include the one-sided endpoints.

For $b\ge0$, all real solutions on the forward interval $[0,b]$ of

$$
y'=\sqrt y,\qquad y(0)=0,\qquad y\ge0
$$

are the waiting-time functions

$$
y(x)=\begin{cases}0,&x\le t,\\(x-t)^2/4,&x>t,\end{cases}
\qquad t\in[0,b].
$$

Here $t=b$ represents the zero solution on the whole interval. If $b>0$, $y=0$ and $y=x^2/4$ are distinct solutions.

**Scope.** The square-root domain condition $y\ge0$ is explicit. The parabola $x^2/4$ is asserted as a solution on a forward interval only, not on negative $x$. No existence theorem for general $\phi$ is claimed.

**Proof.** For two solutions put $w=y-z$. Then $w(a)=0$ and

$$
|w'(x)|=|\phi(x,y(x))-\phi(x,z(x))|\le A|w(x)|.
$$

Exercise 5.26 gives $w=0$. Only values in the specified rectangle are used; no continuity assumption on $\phi$ is needed for this uniqueness implication.

For a waiting-time function, the derivative is zero before $t$ and $(x-t)/2$ after $t$. The difference quotient at $t$ tends to zero from both sides. Since the square root of $(x-t)^2/4$ is $(x-t)/2$ for $x>t$, the equation holds at every point, including the join. The function is nonnegative and has initial value zero. At $b>0$, the zero function and the immediate-start parabola differ at $b$.

Conversely, a solution has nonnegative derivative, so it is nondecreasing. Its zero set in $[0,b]$ is nonempty and compact, by continuity, and has a greatest point $t$. Monotonicity and nonnegativity imply $y=0$ on $[0,t]$, while maximality gives $y>0$ on $(t,b]$. There the chain rule gives

$$
(\sqrt{y})'=\frac{y'}{2\sqrt y}=\frac12.
$$

For any $x>t$, continuity of $\sqrt y$ on $[t,x]$ and the mean value theorem give $\sqrt{y(x)}=(x-t)/2$. Squaring yields the stated branch. This proves both directions of the classification, including $b=0$ and the zero solution.

**Lean declarations:** `exercise27_lipschitz_uniqueness`, `exercise27_nonunique_examples`, `exercise27_sqrt_classification`, `exercise27_all_nonunique_solutions`, `exercise27_wait_solution`.

<a id="r05e28"></a>
### 5.28 — Uniqueness for systems in a cell
**Lean source:** [Exercise28.lean](../../Math/Rudin/Chapter05/Exercise28.lean).
**Inventory status:** Verified as stated.
**Statement.** In $\mathbb R^k$ with Euclidean norm, a function $y$ differentiable within $[a,b]$ with $y(a)=0$ and $\|y'(x)\|\le A\|y(x)\|$ is identically zero, for any real $A$.

Let $C=\prod_{j=1}^k[\alpha_j,\beta_j]$ and let $\Phi:[a,b]\times C\to\mathbb R^k$ satisfy

$$
\|\Phi(x,u)-\Phi(x,v)\|\le A\|u-v\|\qquad(x\in[a,b],\ u,v\in C).
$$

There is at most one differentiable solution with values in $C$ of $y'=\Phi(x,y)$ having a specified initial value $y(a)=c\in C$. Derivatives and the equation hold within the closed interval, including endpoints.

**Proof.** The first assertion is the normed-space differential inequality from Exercise 5.26, specialized to Euclidean space. For two solutions $y,z$ with the same initial value, $w=y-z$ has initial value zero and

$$
\|w'(x)\|=\|\Phi(x,y(x))-\Phi(x,z(x))\|\le A\|w(x)\|.
$$

The first assertion gives $w=0$. The Lipschitz condition is needed only on the specified cell. There is no continuity assumption on the derivative or ambient endpoint derivative assumption. The proof also permits $k=0$, where the vector space has only one element, and degenerate or empty time intervals.

**Lean declarations:** `exercise28_vector_zero_estimate`, `exercise28_system_uniqueness`.

<a id="r05e29"></a>
### 5.29 — Uniqueness for a linear equation of arbitrary positive order
**Lean source:** [Exercise29.lean](../../Math/Rudin/Chapter05/Exercise29.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $k\ge1$, $a\le b$, and let $f,g_1,\ldots,g_k$ be continuous real functions on $[a,b]$. There is at most one real solution with genuine derivatives through order $k$ within $[a,b]$ of

$$
y^{(k)}+g_k y^{(k-1)}+\cdots+g_2y'+g_1y=f,
$$

with initial data $y^{(j-1)}(a)=c_j$ for $1\le j\le k$. The scalar equation and these data are equivalent to the companion system

$$
Y_j'=Y_{j+1}\ (j<k),\qquad
Y_k'=f-\sum_{j=1}^k g_jY_j,\qquad Y_j(a)=c_j,
$$

where $Y_j=y^{(j-1)}$. For $k=1$ this is simply $Y_1'=f-g_1Y_1$.

**Scope.** Derivative data mean functions $D_0,\ldots,D_k$ on the interval with $D_0=y$ and $D_j'=D_{j+1}$ within the interval for every $j<k$, together with the equation and initial data. No continuity of the highest derivative is imposed. For $a<b$, these data agree with the actual iterated within derivatives. The scalar/system equivalence and uniqueness also hold for $a=b$ using the supplied derivative data. Only uniqueness, not existence, is asserted.

**Proof.** Given the scalar derivative data, form the vector $Y=(D_0,\ldots,D_{k-1})$. Coordinatewise differentiation gives the first $k-1$ equations, and the scalar equation gives the last. Conversely, from a system solution take $D_j=Y_{j+1}$ for $0\le j<k$ and $D_k=f-\sum g_jY_j$. The system gives every derivative relation and all initial data. On a nondegenerate interval, uniqueness of within derivatives identifies this supplied sequence inductively with the iterated within derivatives of $y$; this does not infer derivative existence from assigned values.

By compactness and continuity there is a finite $G\ge0$ with $|g_j(x)|\le G$ for every $j,x$. Let $\Phi$ be the companion vector field. The forcing term cancels in $\Phi(x,u)-\Phi(x,v)$. Each of its first $k-1$ coordinates has absolute value at most $\|u-v\|$, and its last has absolute value at most $kG\|u-v\|$. Since the Euclidean norm is at most the sum of the coordinate absolute values, the source's convenient bound is

$$
\|\Phi(x,u)-\Phi(x,v)\|\le k(1+kG)\|u-v\|.
$$

This estimate holds for all vectors. Two proposed system solutions are continuous on the compact interval, so their coordinates lie in a common bounded closed cell. Exercise 5.28 applies on that cell and makes the two vectors equal. Their first coordinates are the scalar solutions, proving uniqueness. The argument includes $k=1$; when $a=b$, equality follows already from the first initial datum. Continuity of $f$ is retained from the statement, although the uniqueness estimate itself only uses the coefficient bounds.

**Lean declarations:** `exercise29_system_reduction`, `exercise29_scalar_iff_iterated`, `exercise29_derivative_tower`, `exercise29_field_order_one`, `exercise29_linear_ode_uniqueness`.

<a id="chapter-06"></a>

## Chapter 6 — The Riemann–Stieltjes Integral

**Exercises:** [1](#r06e01) · [2](#r06e02) · [3](#r06e03) · [4](#r06e04) · [5](#r06e05) · [6](#r06e06) · [7](#r06e07) · [8](#r06e08) · [9](#r06e09) · [10](#r06e10) · [11](#r06e11) · [12](#r06e12) · [13](#r06e13) · [14](#r06e14) · [15](#r06e15) · [16](#r06e16) · [17](#r06e17) · [18](#r06e18) · [19](#r06e19)

Throughout this chapter, $\alpha$ is real-valued. The notation $f\in\mathcal R(\alpha)$ refers to the literal Riemann–Stieltjes integral on the stated compact interval, not to a measure integral obtained by changing $\alpha$. A partition has nodes $a=x_0\le\cdots\le x_n=b$, with $n\ge1$. Its lower and upper sums use the infimum and supremum of $f$ on each **closed** cell, multiplied by $\alpha(x_{i+1})-\alpha(x_i)$. The integrator is nondecreasing on $[a,b]$, the integrand is bounded there, and integrability means that the supremum of lower sums equals the infimum of upper sums. Repeated nodes contribute zero. Thus all integrals over singleton intervals are zero.

The support results prove equivalence with convergence of every tagged refinement of a suitable partition; tags may be cell endpoints. For complex functions, the definition uses norm convergence of the complex tagged sums with these same real increments. This is equivalent to integrability of both real components. No right-continuous normalization of a raw integrator is made. Ordinary Riemann integration means $\alpha(x)=x$.

The support bridges used below have specific scopes. Continuous functions have literal integrals for every interval-nondecreasing $\alpha$, by uniform continuity and small Darboux gaps. Identification with a Stieltjes measure integral requires an already right-continuous Stieltjes function. For the identity integrator, every literal proper Riemann integral equals the Lebesgue interval integral, without extra continuity or measurability assumptions. A bounded function continuous almost everywhere is literally Riemann integrable: closed-cell step envelopes have gaps tending to zero almost everywhere, and dominated convergence makes their integral gaps tend to zero. These bridges justify the measure-theoretic steps below; they do not redefine the source integrals.

<a id="r06e01"></a>
### 6.1 — A function supported at one point
**Lean source:** [Exercise01.lean](../../Math/Rudin/Chapter06/Exercise01.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $a\le b$, $x_0\in[a,b]$, and let $\alpha$ be nondecreasing on $[a,b]$ and continuous at $x_0$ relative to that interval. Define $f(x_0)=1$ and $f(x)=0$ for $x\ne x_0$. Then $f\in\mathcal R(\alpha)$ and

$$
\int_a^b f\,d\alpha=0.
$$

The hypotheses include either endpoint and impose no conditions outside $[a,b]$.

**Proof.** Every positive-length cell contains a point other than $x_0$, so its lower contribution is zero. A zero-length cell also contributes zero. Thus every lower sum is zero, and all upper sums are nonnegative.

If $a<b$, relative continuity gives $u\le x_0\le v$ in $[a,b]$, with $u<v$ and $\alpha(v)-\alpha(u)<\varepsilon$. Choose $u<x_0$ unless $u=a=x_0$, and $x_0<v$ unless $v=b=x_0$. A partition containing $u,v$ isolates the support in $[u,v]$; omit any empty outer interval. Its upper sum is at most $\alpha(v)-\alpha(u)<\varepsilon$. Hence the upper integral is zero as well. If $a=b$, every increment is zero, which proves the same conclusion.

**Lean declarations:** `exercise01`, `exercise01_of_lt`, `pointSpike_lowerSum`, `pointSpike_upperSum_nonneg`, `pointSpike_small_upperSum`.

<a id="r06e02"></a>
### 6.2 — Zero integral and the role of continuity
**Lean source:** [Exercise02.lean](../../Math/Rudin/Chapter06/Exercise02.lean).
**Inventory status:** Verified as stated.

**Statement.** Suppose $a<b$, $f:[a,b]\to\mathbb R$ is continuous and nonnegative, and its ordinary Riemann integral is zero. Then $f(x)=0$ for every $x\in[a,b]$, including the endpoints.

For comparison with Exercise 6.1, the function $h=\mathbf1_{\{1/2\}}$ on $[0,1]$ is nonnegative, has ordinary integral zero, and satisfies $h(1/2)=1$, but is not continuous. Also, the vanishing assertion fails on a singleton interval even for the continuous constant function $1$.

**Proof.** The continuous identity-integrator bridge identifies the given integral with the ordinary interval integral. If $f(x_0)>0$ anywhere in $[a,b]$, continuity gives a relative neighborhood on which $f$ has a positive lower bound. Since $a<b$, that neighborhood contains an interval of positive length, also when $x_0$ is an endpoint. Nonnegativity elsewhere then makes the integral strictly positive, a contradiction.

Exercise 6.1 with $\alpha(x)=x$ proves the zero integral of $h$. Its value at $1/2$ is $1$. If it were continuous on $[0,1]$, the preceding result would force that value to be zero. Finally, $\int_a^a1\,dx=0$, although $1\ne0$ at $a$.

**Scope.** The comparison removes continuity of the **integrand**, not continuity of the integrator in Exercise 6.1. It does not refute the continuous theorem.

**Lean declarations:** `exercise02`, `exercise02_comparison`, `exercise02_singleton_obstruction`.

<a id="r06e03"></a>
### 6.3 — Three values at a jump
**Lean source:** [Exercise03.lean](../../Math/Rudin/Chapter06/Exercise03.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $f:[-1,1]\to\mathbb R$ be bounded. Each $\beta_j$ is zero for $x<0$ and one for $x>0$, while

$$
\beta_1(0)=0,\qquad\beta_2(0)=1,\qquad\beta_3(0)=\tfrac12.
$$

1. $f\in\mathcal R(\beta_1)$ if and only if $\lim_{x\downarrow0}f(x)=f(0)$.
2. $f\in\mathcal R(\beta_2)$ if and only if $\lim_{x\uparrow0}f(x)=f(0)$.
3. $f\in\mathcal R(\beta_3)$ if and only if $f$ is continuous at zero.
4. Every integral that exists in these cases equals $f(0)$. In particular, continuity at zero gives all three integrals and the same value. No continuity away from zero is required.

**Proof.** More generally, put $\beta(0)=c$ with $0\le c\le1$. A cell with nonzero increment must contain zero. Tag every such cell at zero. The sum is then exactly $f(0)$, because all increments telescope to $1$. Consequently any integral value must be $f(0)$.

Suppose the tagged sums converge. In a partition controlling their error, change one tag in a cell containing zero from $0$ to $y$. The resulting error is

$$
|f(y)-f(0)|\,|\beta(x_{i+1})-\beta(x_i)|.
$$

The cell where the partition first crosses into $(0,1]$ has increment at least $1-c$. If $c<1$, control of this error forces right continuity at zero. The cell where it first reaches $[0,1]$ from the left has increment at least $c$; if $c>0$, the same argument forces left continuity.

Conversely, assume continuity on each side whose coefficient is nonzero. Insert $-d,0,d$ into a partition, with $0<d\le1$ sufficiently small. In every refinement, cells with nonzero increments lie on the required side within distance $d$ of zero. Their tag values differ from $f(0)$ by less than $\varepsilon$. The absolute error is at most $\varepsilon$ times the total increment, which is $1$. A side with coefficient zero contributes nothing and needs no continuity. Apply this with $c=0,1,1/2$ and use the proved Darboux–tagged equivalence.

**Scope.** The actual values $\beta_j(0)$ are essential. Replacing them by right limits would change the problem.

**Lean declarations:** `exercise03_a_integrability`, `exercise03_a_integral`, `exercise03_a_value`, `exercise03_b_integrability`, `exercise03_b_integral`, `exercise03_b_value`, `exercise03_c_integrability`, `exercise03_c_integral`, `exercise03_c_value`, `exercise03_d`, `exercise03_beta_negative`, `exercise03_beta_positive`.

<a id="r06e04"></a>
### 6.4 — The rational indicator is not Riemann integrable
**Lean source:** [Exercise04.lean](../../Math/Rudin/Chapter06/Exercise04.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $D(x)=1$ on rational points and $D(x)=0$ on irrational points. For $a\le b$, its lower Darboux integral is $0$ and its upper Darboux integral is $b-a$. Thus it is not Riemann integrable when $a<b$, either in the Darboux or equivalent tagged sense. The same holds for any function with these values on $[a,b]$, regardless of its values outside that interval.

**Proof.** Both rational and irrational points occur in every positive-length cell. Its infimum is therefore $0$ and its supremum is $1$. Repeated-node cells have zero weight. Every lower sum is $0$, while every upper sum is

$$
\sum_i(x_{i+1}-x_i)=b-a.
$$

Taking the two extrema gives the stated values. They differ precisely when $a<b$. On a singleton they both vanish. Equality of functions on the interval preserves all these sums, which gives the final formulation.

**Lean declarations:** `exercise04`, `exercise04_source`, `exercise04_darboux_extrema`, `exercise04_tagged`, `rationalIndicator_lowerSum`, `rationalIndicator_upperSum`.

<a id="r06e05"></a>
### 6.5 — Integrable squares and cubes
**Lean source:** [Exercise05.lean](../../Math/Rudin/Chapter06/Exercise05.lean).
**Inventory status:** Verified as stated.

**Statement.** For bounded real functions, integrability of $f^2$ does not imply integrability of $f$ on a nondegenerate interval. In contrast, if $a\le b$ and $f^3\in\mathcal R(\alpha)$, then $f\in\mathcal R(\alpha)$. This includes ordinary Riemann integrals and the equivalent tagged formulation.

**Proof.** Let $f=2D-1$, with $D$ from Exercise 6.4. Then $f$ is $1$ on rational points and $-1$ on irrational points; hence $|f|=1$, $f^2=1$, and $\int_a^bf^2\,dx=b-a$, including $a=b$. If $f$ were integrable for $a<b$, linearity would make $D=(f+1)/2$ integrable, contrary to Exercise 6.4.

For the cube, use the continuous signed cube root

$$
r(y)=(\max(y,0))^{1/3}-(\max(-y,0))^{1/3}.
$$

Both power bases are nonnegative. Splitting into $y\ge0$ and $y\le0$ proves continuity at all points, $r(x^3)=x$, and $r(y)^3=y$, including negative inputs and zero. The bounded range of the integrable function $f^3$ lies in a compact interval. The continuous-composition theorem for literal Riemann–Stieltjes integrals therefore makes $r\circ f^3=f$ integrable.

**Scope.** The cube theorem needs no separate bound on $f$: boundedness of $f^3$, already included in its integrability, suffices. The assertion is for real functions, not arbitrary complex cube roots.

**Lean declarations:** `exercise05_square`, `exercise05_square_integral`, `exercise05_sign_nonintegrable`, `exercise05_cube`, `exercise05_cube_stieltjes`, `exercise05_cube_tagged`, `continuous_signedCubeRoot`, `signedCubeRoot_cube`, `cube_signedCubeRoot`.

<a id="r06e06"></a>
### 6.6 — Discontinuities confined to the Cantor set
**Lean source:** [Exercise06.lean](../../Math/Rudin/Chapter06/Exercise06.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $P$ be the middle-thirds Cantor set. Suppose $f:[0,1]\to\mathbb R$ satisfies $|f(x)|\le M$ and is continuous relative to $[0,1]$ at every point outside $P$. Then $f$ is ordinarily Riemann integrable, and its literal integral equals its Lebesgue interval integral. No continuity is required at points of $P$, including $0$ and $1$.

**Proof.** The compact set $P$ has finite Lebesgue measure $m$. Its self-similarity is

$$
P=\tfrac13P\ \cup\ \tfrac13(2+P).
$$

Translation invariance and scaling of Lebesgue measure give $m\le m/3+m/3$. Finiteness and nonnegativity imply $m=0$. Thus the given bounded function is relatively continuous almost everywhere. The support criterion described above supplies arbitrarily small literal Darboux gaps and the asserted integral, not merely an almost-everywhere replacement of $f$.

**Lean declarations:** `exercise06`, `exercise06_cantor_null`.

<a id="r06e07"></a>
### 6.7 — Proper and conditionally convergent improper integrals
**Lean source:** [Exercise07.lean](../../Math/Rudin/Chapter06/Exercise07.lean).
**Inventory status:** Verified as stated.

**Statement.** An improper integral at a finite left endpoint $a<b$ means a finite limit

$$
\lim_{c\downarrow a}\int_c^b f(x)\,dx,
$$

with an actual proper Riemann integral on every $[c,b]$, $a<c\le b$. At infinity it means a finite limit of $\int_a^B f$ as $B\to\infty$, with actual proper integrals for every $B\ge a$. These definitions include the singleton truncations and assign no value to divergence.

1. If $f$ is properly Riemann integrable on $[a,b]$, $a<b$, with integral $v$, its improper integral at $a$ exists and equals $v$. In particular this applies to $[0,1]$.
2. On $(0,1]$, the explicit function

   $$
   f(x)=\frac{\cos(1/x-1)}x
   $$

   has a finite improper integral, but $|f|$ does not. Both have proper integrals on every $[c,1]$, $0<c\le1$.

**Proof.** For the first assertion, restriction preserves proper integrability. The ordinary bridge gives an integrable function on the compact interval with the same value $v$. Continuity of its integral with respect to the lower endpoint then gives the required limit. Neither continuity nor prior measurability of $f$ is assumed.

For the construction, define, for $k\ne0$ and $t\ge0$,

$$
K_k(t)=\frac{\cos(kt)}{1+t},\qquad H_k(t)=\frac{\sin(kt)}{(1+t)^2}.
$$

These functions are continuous on each truncation. Integration by parts gives

$$
\int_0^B K_k(t)\,dt
=\frac{\sin(kB)}{k(1+B)}+\frac1k\int_0^B H_k(t)\,dt.
$$

The boundary term tends to zero, and $|H_k(t)|\le(1+t)^{-2}$ proves absolute convergence of the second integral. Thus every $K_k$ has a finite improper integral.

The integral of $|K_1|$ cannot converge finitely. Otherwise the nonnegative-improper-integral bridge would give absolute integrability of $K_1$. Since $\cos^2t\le|\cos t|$, the integral of $\cos^2t/(1+t)$ would also converge. But $2\cos^2t-\cos(2t)=1$ implies

$$
2\int_0^B\frac{\cos^2t}{1+t}\,dt-\int_0^BK_2(t)\,dt=\log(1+B),
$$

contradicting the finite limits on the left.

Finally, the proper substitution $t=1/x-1$ gives

$$
\int_c^1f(x)\,dx=\int_0^{1/c-1}K_1(t)\,dt,\qquad
\int_c^1|f(x)|\,dx=\int_0^{1/c-1}|K_1(t)|\,dt.
$$

It follows that the first limit exists, with value $\int_0^\infty H_1(t)\,dt$. A finite limit for the second would, on setting $c=(1+B)^{-1}$, contradict the preceding nonconvergence. Continuity away from zero supplies all proper witnesses.

**Lean declarations:** `exercise07_a`, `exercise07_b`, `properRiemann_of_continuousOn`, `properRiemann_restrict_right`, `improperRiemannTop_of_integrableOn`, `integrableOn_of_improperRiemannTop_nonneg`, `oscillatoryKernel_proper_identity`, `oscillatoryKernel_improper`, `oscillatoryKernel_one_not_absolute`, `inverse_substitution`, `conditionalEndpointExample_proper`.

<a id="r06e08"></a>
### 6.8 — The integral test
**Lean source:** [Exercise08.lean](../../Math/Rudin/Chapter06/Exercise08.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $f:[1,\infty)\to\mathbb R$ be nonnegative and nonincreasing. Then

$$
\int_1^\infty f(x)\,dx\text{ converges finitely}
\quad\Longleftrightarrow\quad
\sum_{n=1}^\infty f(n)\text{ converges}.
$$

Series convergence means convergence of the ordered partial sums. Monotonicity alone supplies the proper Riemann integrals on every $[1,B]$, including $B=1$.

**Proof.** On $[n,n+1]$, monotonicity gives

$$
f(n+1)\le\int_n^{n+1}f(x)\,dx\le f(n).
$$

Consequently, for $N\ge1$,

$$
\sum_{n=2}^{N+1}f(n)\le\int_1^{N+1}f(x)\,dx\le\sum_{n=1}^Nf(n).
$$

All these partial sums and integral truncations are nondecreasing. A finite improper limit bounds the left sums, which therefore converge. Conversely, bounded partial sums bound the integral at integer endpoints; monotonicity bounds every real truncation by a larger integer truncation. Thus the truncations have a finite limit. The Lean proof uses the corresponding standard sum–integral comparison theorems through the ordinary bridge. It proves the equivalence between ordered convergence and summability for these nonnegative terms; unconditional summability is not an extra assumption.

**Lean declarations:** `exercise08_integral_test`, `exercise08_proper`, `ordinarySeriesConverges_iff_summable_of_nonneg`.

<a id="r06e09"></a>
### 6.9 — Integration by parts at improper endpoints
**Lean source:** [Exercise09.lean](../../Math/Rudin/Chapter06/Exercise09.lean).
**Inventory status:** Verified as stated.

**Statement.** The following sufficient rules use real functions and explicit local $C^1$ data.
1. Let $a<b$. Suppose $u,v$ have derivatives $u',v'$ relative to $(a,b]$ at every point there, and $u',v'$ are continuous on $(a,b]$. If $u(x)v(x)\to L$ as $x\downarrow a$ and $\int_a^b u'v=I$ exists improperly, then

   $$
   \int_a^b uv'=u(b)v(b)-L-I.
   $$

2. Suppose instead that these derivative and continuity conditions hold on $[a,\infty)$. If $u(x)v(x)\to L$ at infinity and $\int_a^\infty u'v=I$ exists improperly, then

   $$
   \int_a^\infty uv'=L-u(a)v(a)-I.
   $$

3. Both improper integrals below converge and are equal:

   $$
   \int_0^\infty\frac{\cos x}{1+x}\,dx
      =\int_0^\infty\frac{\sin x}{(1+x)^2}\,dx.
   $$

   The right integral converges absolutely; the left does not.

**Proof.** Relative derivatives permit the appropriate one-sided derivatives at included endpoints. They also give continuity of $u,v$. On every closed truncation the products are continuous, so both proper integrals exist. Proper integration by parts gives

$$
\int_c^Buv'=u(B)v(B)-u(c)v(c)-\int_c^Bu'v.
$$

Taking the indicated limit proves each rule and constructs the other improper integral. No derivative is assumed at the omitted endpoint.

For the example take $u(x)=(1+x)^{-1}$ and $v(x)=\sin x$. Then $u'v=-\sin x/(1+x)^2$, the boundary product is zero at $0$ and tends to zero at infinity. The bound $|\sin x|/(1+x)^2\le(1+x)^{-2}$ gives absolute convergence of the right integral. The second rule gives the equality. The double-angle/logarithm argument in Exercise 6.7 proves failure of absolute convergence on the left. All four integrands, including the two absolute values, are continuous on each $[0,B]$, so their proper integral witnesses exist even at $B=0$.

**Lean declarations:** `exercise09_finite_endpoint_rule`, `exercise09_infinite_endpoint_rule`, `exercise09_example_equality`, `exercise09_sine_absolute`, `exercise09_cosine_not_absolute`, `properRiemann_integration_by_parts`, `exercise09_proper`.

<a id="r06e10"></a>
### 6.10 — Young and Hölder inequalities
**Lean source:** [Exercise10.lean](../../Math/Rudin/Chapter06/Exercise10.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $p,q>0$ satisfy $1/p+1/q=1$; these conditions imply $p,q>1$.
1. For $u,v\ge0$,

   $$
   uv\le\frac{u^p}{p}+\frac{v^q}{q},
   $$

   with equality exactly when $u^p=v^q$, including $u=v=0$.
2. On $a\le b$, let $\alpha$ be nondecreasing and let real nonnegative $f,g\in\mathcal R(\alpha)$ satisfy $\int f^p\,d\alpha=\int g^q\,d\alpha=1$. Then $fg$ is integrable and $\int fg\,d\alpha\le1$.
3. For complex $f,g\in\mathcal R(\alpha)$ on $a\le b$, the product and both norm powers are integrable, and

   $$
   \left|\int_a^b fg\,d\alpha\right|
      \le\left(\int_a^b|f|^p\,d\alpha\right)^{1/p}
          \left(\int_a^b|g|^q\,d\alpha\right)^{1/q}.
   $$

   Zero power integrals, zero total increment, jumps, and singleton intervals are included.
4. The same Hölder bound holds for ordinary improper integrals on $[a,\infty)$ and on $(a,b]$, $a<b$. Here $f,g$ are complex-valued and properly Riemann integrable on **every** closed truncation, including singleton cuts. Assume the improper integrals of $|f|^p$ and $|g|^q$ have finite values $A,B$. Then the product has proper integrals on every truncation and a finite improper value $z$, with $|z|\le A^{1/p}B^{1/q}$. Product convergence is a conclusion, not a hypothesis.

**Proof.** Young's inequality and its exact equality condition are the standard nonnegative form of Young's theorem. Continuous composition gives the required powers; the product closure law constructs the product integral. Integrating Young's inequality proves the normalized assertion.

To include zero norms without division, apply finite Hölder directly to the actual nonnegative weights $w_i=\alpha(x_{i+1})-\alpha(x_i)$:

$$
\sum_i F_iG_iw_i\le
\left(\sum_iF_i^pw_i\right)^{1/p}
\left(\sum_iG_i^qw_i\right)^{1/q}.
$$

This follows by applying unweighted finite Hölder to $F_iw_i^{1/p}$ and $G_iw_i^{1/q}$. Choose common refinements whose tagged sums approximate the three integrals with errors tending to zero. Continuity of the positive powers, also at zero, gives the real integral inequality. For complex functions the norm of the integral is at most the integral of the norm, and $|fg|=|f||g|$; apply the real inequality to these two norms. Component and composition results supply all integral-existence statements.

For the improper cases, on each truncation Young gives

$$
\int|fg|\le\frac1p\int|f|^p+\frac1q\int|g|^q.
$$

The assumed finite power limits bound these nonnegative truncations. The ordinary real and componentwise complex bridges, followed by the bounded-truncation criterion, prove absolute integrability of the product on the ray or the finite half-open interval. Thus its proper integrals have a finite limit. Passing to the limit in the proper Hölder inequality gives the required bound, again without dividing by $A$ or $B$.

**Scope.** The improper assertions use the identity integrator. They do not assert an improper theorem for an arbitrary raw Stieltjes integrator.

**Lean declarations:** `young`, `young_eq_iff`, `holder_normalized`, `holder_complex`, `holder_improper_left_complex`, `holder_improper_top_complex`, `weighted_holder`, `holder_real_values`, `holder_complex_values`, `exists_rs_rpow`, `exists_complex_norm_rpow`, `complex_ordinary_integral`, `proper_complex_product`, `proper_product_norm_young`.

<a id="r06e11"></a>
### 6.11 — The weighted quadratic seminorm
**Lean source:** [Exercise11.lean](../../Math/Rudin/Chapter06/Exercise11.lean).
**Inventory status:** Verified as stated.

**Statement.** For $a\le b$, nondecreasing $\alpha$, and complex $u\in\mathcal R(\alpha)$, define

$$
\|u\|_2=\left(\int_a^b|u|^2\,d\alpha\right)^{1/2}.
$$

The integral exists and this quantity is nonnegative. For $f,g,h\in\mathcal R(\alpha)$,

$$
\|f-h\|_2\le\|f-g\|_2+\|g-h\|_2.
$$

The same assertion holds for real functions under their canonical complex embedding. This is a seminorm on actual functions; no separation assertion is made.

**Proof.** Composition gives each squared-norm integral. Put $A=\int|u|^2$, $B=\int|v|^2$, and $C=\int|u||v|$, all with respect to $\alpha$. Schwarz, the $p=q=2$ case of Exercise 6.10, gives $C\le\sqrt A\sqrt B$. The pointwise triangle inequality yields

$$
\int|u+v|^2\le A+2C+B\le(\sqrt A+\sqrt B)^2.
$$

All quantities are nonnegative, so taking square roots proves $\|u+v\|_2\le\|u\|_2+\|v\|_2$. Apply it to $u=f-g$ and $v=g-h$. Real embedding preserves the actual integral and the absolute value, giving the real case. For the zero integrator every increment vanishes, so even the constant function $1$ has seminorm zero.

**Scope.** The implementation selects the unique raw integral value when it exists, with a default value outside that domain. Every use in these inequalities proves existence first; the default is not an integrability claim.

**Lean declarations:** `rsL2Norm_difference_triangle`, `rsL2Norm_real_difference_triangle`, `exists_l2_integral`, `rsL2Norm_eq`, `rsL2Norm_nonneg`, `schwarz_norm_values`, `rsL2Norm_add_le`, `hasComplexRSIntegral_real`, `rsL2Norm_constant_one_zero_integrator`.

<a id="r06e12"></a>
### 6.12 — Continuous approximation in the quadratic seminorm
**Lean source:** [Exercise12.lean](../../Math/Rudin/Chapter06/Exercise12.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $a\le b$, let $\alpha$ be nondecreasing on $[a,b]$, let $f\in\mathcal R(\alpha)$ be complex-valued, and let $\varepsilon>0$. There is a continuous function $g:\mathbb R\to\mathbb C$, itself integrable against $\alpha$, such that its actual squared-error integral $E$ satisfies

$$
0\le E=\int_a^b|f-g|^2\,d\alpha<\varepsilon^2,
\qquad\|f-g\|_2<\varepsilon.
$$

When $f$ is real, $g$ can be real. No continuity of $\alpha$ or positive total increment is assumed.

**Proof.** First suppose $f$ is real and $|f|\le M$ on the interval, with $M\ge0$. Choose a partition $P$ with

$$
U(P,f,\alpha)-L(P,f,\alpha)<\frac{\delta}{2M+1}.
$$

Interpolate the values $f(x_i)$ linearly on each positive-length cell, and extend constantly outside $[a,b]$. One global formula is

$$
g(t)=f(a)+\sum_i r_i(t)\bigl(f(x_{i+1})-f(x_i)\bigr),\qquad
r_i(t)=\min\!\left(1,\max\!\left(0,\frac{t-x_i}{x_{i+1}-x_i}\right)\right).
$$

For repeated nodes the coefficient difference is zero; omit that term, so no division by zero is needed in this mathematical formula. On a genuine cell, $g$ is the convex combination of its two endpoint values. Hence both $f(t)$ and $g(t)$ lie between the closed-cell extrema $m_i,M_i$. Thus

$$
|f(t)-g(t)|^2\le2M(M_i-m_i).
$$

The continuous-integrand existence theorem and algebraic closure show that $g$ and $(f-g)^2$ have actual raw integrals. Their upper-sum bound gives

$$
0\le E\le U(P,(f-g)^2,\alpha)
\le2M\bigl(U(P,f,\alpha)-L(P,f,\alpha)\bigr)<\delta.
$$

Choose $\delta=\varepsilon^2$ for the real assertion.

For complex $f$, apply this construction separately to its real and imaginary parts with $\delta=\varepsilon^2/2$. Combine the two real polygons into $g$. The identity $|f-g|^2=(\Re(f-g))^2+(\Im(f-g))^2$ gives $E<\varepsilon^2$. Taking the nonnegative square root proves the seminorm estimate. The argument uses the actual closed-cell gaps and therefore also covers jumps of $\alpha$, zero mass, and $a=b$.

**Lean declarations:** `continuous_approximation_complex`, `continuous_approximation_real`, `exists_continuous_real_sq_error`, `exists_continuous_complex_rs`, `partitionPolygon_cell_affine`, `partitionPolygon_error_bound`, `partitionPolygon_upper_error_le`.

<a id="r06e13"></a>
### 6.13 — A quadratic oscillatory phase
**Lean source:** [Exercise13.lean](../../Math/Rudin/Chapter06/Exercise13.lean).
**Inventory status:** Verified as stated.

**Statement.** Define, for real $x$,

$$
F(x)=\int_x^{x+1}\sin(t^2)\,dt.
$$

Every such integral, and every finite truncation of $\sin(t^2)$, is a proper Riemann integral.
1. For $x>0$, $|F(x)|<1/x$.
2. For $x>0$,

   $$
   2xF(x)=\cos(x^2)-\cos((x+1)^2)+r(x),\qquad |r(x)|<2/x.
   $$

3. $\limsup_{x\to\infty}xF(x)=1$ and $\liminf_{x\to\infty}xF(x)=-1$; actual sequences tending to infinity approach both values.
4. $\int_0^\infty\sin(t^2)\,dt$ converges as a finite limit of proper Riemann integrals.

**Proof.** Continuity gives every proper integral. Integration by parts on $0<a\le b$ gives

$$
\int_a^b\sin(t^2)\,dt
=\frac{\cos(a^2)}{2a}-\frac{\cos(b^2)}{2b}
-\int_a^b\frac{\cos(t^2)}{2t^2}\,dt.
$$

The last integral has absolute value at most $1/(2a)-1/(2b)$. For $a<b$ the inequality is strict: $|\cos(t^2)|$ cannot be identically $1$ on a nondegenerate positive interval. Otherwise $\sin(t^2)$ would vanish there, while its derivative $2t\cos(t^2)$ would not. Continuity makes the strict pointwise inequality strict after integration. Combining the three bounds gives $|F(x)|<1/x$ and the uniform tail bound

$$
\left|\int_a^b\sin(t^2)\,dt\right|\le1/a.
$$

The latter is the Cauchy criterion at infinity, proving part 4 with all proper witnesses.

Multiplying the integration-by-parts formula by $2x$ gives part 2 with

$$
r(x)=\frac{\cos((x+1)^2)}{x+1}
-2x\int_x^{x+1}\frac{\cos(t^2)}{2t^2}\,dt.
$$

Its absolute value is at most $2/(x+1)<2/x$, hence tends to zero.

To attain both limiting bounds, set

$$
y_n=\pi(n+1)+\frac{\pi-1}{2},\quad
m_n(\delta)=\left\lfloor\frac{y_n^2-\delta}{2\pi}\right\rfloor,\quad
x_n(\delta)=\sqrt{2\pi m_n(\delta)+\delta},
$$

for $\delta=0$ or $\pi$. The floor arguments are nonnegative. The floor inequalities give $x_n\le y_n$ and $|x_n-y_n|\le2\pi/y_n\to0$, so $x_n\to\infty$. Moreover,

$$
\cos(x_n^2)=\cos\delta,\qquad
\cos((x_n+1)^2)=\cos\bigl(\delta+\pi+2(x_n-y_n)\bigr).
$$

The asymptotic formula therefore gives $x_nF(x_n)\to1$ for $\delta=0$ and $\to-1$ for $\delta=\pi$. Part 1 bounds all sufficiently large scaled values between $-1$ and $1$, which proves the limsup and liminf assertions.

**Lean declarations:** `quadraticWindow_hasDarboux`, `quadratic_hasDarboux`, `exercise13_a`, `exercise13_b`, `exercise13_c`, `exercise13_c_sequences`, `exercise13_d`, `quadratic_tail_bound`, `quadratic_integration_by_parts`, `quadraticRemainder_tendsto`.

<a id="r06e14"></a>
### 6.14 — An exponential oscillatory phase
**Lean source:** [Exercise14.lean](../../Math/Rudin/Chapter06/Exercise14.lean).
**Inventory status:** Verified as stated.

**Statement.** For real $x$, let

$$
F(x)=\int_x^{x+1}\sin(e^t)\,dt.
$$

All finite truncations are proper Riemann integrals. For **every real** $x$,

$$
e^x|F(x)|<2,
$$

$$
e^xF(x)=\cos(e^x)-e^{-1}\cos(e^{x+1})+r(x),\qquad |r(x)|<3e^{-x}.
$$

Furthermore,

$$
\limsup_{x\to\infty}e^xF(x)=1+e^{-1},\qquad
\liminf_{x\to\infty}e^xF(x)=-(1+e^{-1}),
$$

with sequences attaining both limits, and $\int_0^\infty\sin(e^t)\,dt$ converges improperly.

**Proof.** Continuity supplies all proper integrals. Integration by parts gives

$$
\int_a^b\sin(e^t)\,dt
=e^{-a}\cos(e^a)-e^{-b}\cos(e^b)
-\int_a^be^{-t}\cos(e^t)\,dt.
$$

For $a\le b$, the correction has absolute value at most $e^{-a}-e^{-b}$, and the bound is strict when $a<b$. Indeed, $|\cos(e^t)|$ cannot be constantly $1$ on an interval, since the phase derivative $e^t$ never vanishes. Thus $|F(x)|<2e^{-x}$ for all real $x$. The non-strict estimate on arbitrary tails is

$$
\left|\int_a^b\sin(e^t)\,dt\right|\le2e^{-a},
$$

which proves improper convergence by the Cauchy criterion.

For the sharper remainder, a second integration by parts gives

$$
\int_a^be^{-t}\cos(e^t)\,dt
=e^{-2b}\sin(e^b)-e^{-2a}\sin(e^a)
+2\int_a^be^{-2t}\sin(e^t)\,dt.
$$

Its absolute value is at most $2e^{-2a}$. Taking

$$
r(x)=-e^x\int_x^{x+1}e^{-t}\cos(e^t)\,dt
$$

proves the displayed identity and $|r(x)|\le2e^{-x}<3e^{-x}$.

The identity bounds all limiting values by $\pm(1+e^{-1})$. To attain the bounds, use irrationality of $e$ and density of irrational rotations modulo $2\pi$. For any $\delta\ge0$ and target $\beta$, choose increasing integers $n_j$ such that

$$
e\bigl(\delta+2\pi(n_j+1)\bigr)\pmod{2\pi}\longrightarrow\beta\pmod{2\pi}.
$$

With $x_j=\log(\delta+2\pi(n_j+1))$, one has $x_j\to\infty$, $\cos(e^{x_j})=\cos\delta$, and $\cos(e^{x_j+1})\to\cos\beta$. The remainder tends to zero. The choices $(\delta,\beta)=(0,\pi)$ and $(\pi,0)$ yield the two claimed extremal limits.

**Scope.** Repeating Exercise 6.13 includes the limit and convergence questions. The sharp scaled limits here are $\pm(1+e^{-1})$, not $\pm2$; the strict bound $2$ alone does not determine them.

**Lean declarations:** `exponentialWindow_hasDarboux`, `exponential_hasDarboux`, `exercise14_decay_bound`, `exercise14_asymptotic`, `exercise14_limits`, `exercise14_limit_sequences`, `exercise14_improper_convergence`, `exponential_tail_bound`, `exponential_second_integration_by_parts`, `exponentialRemainder_tendsto`, `exponential_phase_irrational`, `exponential_phase_sequence`.

<a id="r06e15"></a>
### 6.15 — A strict Schwarz-type bound
**Lean source:** [Exercise15.lean](../../Math/Rudin/Chapter06/Exercise15.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $a\le b$ and let real $f$ have derivative $f'$ relative to $[a,b]$ at every point, including one-sided endpoint derivatives. Assume $f'$ is continuous on $[a,b]$, $f(a)=f(b)=0$, and the actual Riemann integral satisfies $\int_a^bf^2\,dx=1$. Then all the following integrals exist properly, and

$$
\int_a^bxf(x)f'(x)\,dx=-\tfrac12,
$$

$$
\left(\int_a^b(f')^2\,dx\right)
\left(\int_a^bx^2f^2\,dx\right)>\tfrac14.
$$

The normalization rules out $a=b$.

**Proof.** The derivative hypotheses give continuity of $f$, and all displayed integrands are continuous. Integrate

$$
(xf^2)'=f^2+2xff'.
$$

The endpoint terms vanish and $\int f^2=1$, proving the first identity.

For each real $c$, the integral $\int_a^b(f'+cxf)^2\,dx$ is strictly positive. If the continuous nonnegative integrand had zero integral, it would vanish everywhere, so $f'=-cxf$. On this compact interval,

$$
|f'|\le |c|(|a|+|b|)|f|.
$$

The zero-solution theorem for this differential inequality, with $f(a)=0$, forces $f=0$, contradicting the normalization.

Put $A=\int_a^b(f')^2\,dx\ge0$ and $B=\int_a^bx^2f^2\,dx$. Apply the strict positivity just proved with $c=2A$. Expanding the square and using the first identity gives

$$
0<A+4A(-\tfrac12)+4A^2B=A(4AB-1).
$$

Since $A\ge0$, this forces $AB>1/4$. This explicitly excludes equality rather than assuming a strict version of Schwarz.

**Lean declarations:** `exercise15_integration_identity`, `exercise15_strict_product_bound`, `exercise15`.

<a id="r06e16"></a>
### 6.16 — Floor-function integral formulas for zeta
**Lean source:** [Exercise16.lean](../../Math/Rudin/Chapter06/Exercise16.lean).
**Inventory status:** Verified as stated.

**Statement.** For $s>1$, the ordered series $\zeta(s)=\sum_{n=1}^\infty n^{-s}$ converges, and

$$
\zeta(s)=s\int_1^\infty\frac{\lfloor x\rfloor}{x^{s+1}}\,dx,
$$

$$
\zeta(s)=\frac{s}{s-1}-s\int_1^\infty\frac{x-\lfloor x\rfloor}{x^{s+1}}\,dx.
$$

Both formulas use actual improper Riemann integrals. The remainder integral converges for every real $s>0$. For every real $s$ and every $B\ge1$, both integrands have proper Riemann integrals on $[1,B]$. The exact finite identity, valid for every real $s$ and integer $N\ge1$, is

$$
\sum_{n=1}^N n^{-s}=N^{1-s}+s\int_1^N\frac{\lfloor x\rfloor}{x^{s+1}}\,dx.
$$

**Proof.** On each compact interval starting at $1$, the floor function is monotone and hence properly Riemann integrable. The factor $x^{-s-1}$ is continuous there. Product and subtraction laws give proper integrability of both displayed integrands for all real $s$, also at $B=1$.

Abel summation applied to $x^{-s}$, whose derivative is $-sx^{-s-1}$ for $x>0$, gives the finite identity. For $s>1$, the $p$-series theorem gives ordered convergence, while

$$
0\le\frac{\lfloor x\rfloor}{x^{s+1}}\le x^{-s}\qquad(x\ge1)
$$

proves convergence of the floor integral over all real cutoffs. Letting $N\to\infty$ in the finite identity, with $N^{1-s}\to0$, proves the first formula.

For $s>0$,

$$
0\le\frac{x-\lfloor x\rfloor}{x^{s+1}}\le x^{-s-1},
$$

and the comparison integral is finite. Together with the proper witnesses this proves convergence of the remainder. If $s>1$, the two integrands add to $x^{-s}$, whose integral from $1$ to infinity is $1/(s-1)$. Adding their truncations and taking limits gives the second formula.

**Scope.** Only the remainder convergence is extended to $0<s\le1$. No convergence of the defining zeta series, or zeta formula on that range, is asserted.

**Lean declarations:** `exercise16_a`, `exercise16_ordered_series`, `exercise16_proper_integrals`, `exercise16_finite_identity`, `exercise16_b`, `exercise16_remainder_convergence`.

<a id="r06e17"></a>
### 6.17 — Integration by parts with a discontinuous monotone factor
**Lean source:** [Exercise17.lean](../../Math/Rudin/Chapter06/Exercise17.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $a\le b$, let real $\alpha$ be nondecreasing on $[a,b]$, let $g$ be continuous there, and suppose $G'=g$ relative to $[a,b]$ at every point, with one-sided endpoint derivatives. Then both literal integrals exist and

$$
\int_a^b\alpha(x)g(x)\,dx
=\alpha(b)G(b)-\alpha(a)G(a)-\int_a^bG\,d\alpha.
$$

The assertion holds for real $g,G$ and also for complex $g,G$ with a real parameter derivative. In the complex case multiplication by $\alpha$ is real scalar multiplication. No continuity of $\alpha$ is assumed, even at endpoints.

**Proof.** Monotonicity makes $\alpha$ ordinarily Riemann integrable, and continuity makes $g$ so; their product is integrable. The derivative condition makes $G$ continuous, hence $G\in\mathcal R(\alpha)$. This constructs both integrals before proving their relation.

For a partition, finite summation by parts gives the exact identity

$$
\sum_iG(x_{i+1})\bigl(\alpha(x_{i+1})-\alpha(x_i)\bigr)
+\sum_i\alpha(x_i)\bigl(G(x_{i+1})-G(x_i)\bigr)
=\alpha(b)G(b)-\alpha(a)G(a).
$$

Uniform differentiability, which follows from the continuous derivative on the compact interval, gives

$$
|G(y)-G(x)-g(x)(y-x)|\le\eta|y-x|
$$

for sufficiently close points of $[a,b]$. If $|\alpha|\le C$, replacing the second sum by its left-tag ordinary sum changes it by at most $C\eta(b-a)$. Zero-length cells give zero error. Take a common refinement that both controls the two integrals and has sufficiently short cells. The first sum tends to $\int G\,d\alpha$, the replaced sum tends to $\int\alpha g\,dx$, and the error tends to zero. The displayed formula follows with the original endpoint values of $\alpha$. Apply this real proof to real and imaginary components for the complex assertion. At $a=b$ all terms cancel directly.

**Lean declarations:** `exercise17_stieltjes_parts`, `exercise17_stieltjes_parts_complex`.

<a id="r06e18"></a>
### 6.18 — The same circle with different lengths
**Lean source:** [Exercise18.lean](../../Math/Rudin/Chapter06/Exercise18.lean).
**Inventory status:** Verified refutation and correction.

**Statement.** On $[0,2\pi]$, define complex curves

$$
\gamma_1(t)=e^{it},\qquad\gamma_2(t)=e^{2it},\qquad
\gamma_3(t)=\begin{cases}1,&t=0,\\
\exp\bigl(2\pi i\,t\sin(1/t)\bigr),&t>0.
\end{cases}
$$

All three are continuous and have the unit circle as their range. The first two are rectifiable, with lengths $2\pi$ and $4\pi$. The third has infinite length and infinite variation, and is not rectifiable. Length is the supremum of ordered partition chord sums in the usual complex norm, as in Exercise 6.19.

**Correction.** The printed third formula contains $1/t$ but its interval includes zero. There is no real reciprocal of zero: no real $u$ satisfies $0u=1$. The value $\gamma_3(0)=1$ is an explicit endpoint repair and is the **unique** continuous extension of the printed positive-parameter formula. The phase remains $t\sin(1/t)$, not $\sin(1/t)$ alone. The inventory records a verified refutation and explicit correction, not a proof of the unextended printed formula.

**Proof.** The bound $|t\sin(1/t)|\le|t|$ makes the phase tend to zero as $t\to0$. Thus the positive-parameter formula tends to $1$, proving continuity of the repair and uniqueness of its endpoint value. Away from zero continuity follows by composition. The first two curves are continuous directly.

Every value has modulus one. The first curve covers the circle over a full angular period; the second covers it as well by taking half of each first-curve parameter. For the third curve put $h(t)=t\sin(1/t)$ and $l=2/(3\pi)$. Then $h(l)=-2/(3\pi)$, while the inequality $\sin u\ge u-u^3/6$ gives

$$
h(2\pi)\ge1-\frac1{24\pi^2}.
$$

Since $1/(24\pi^2)\le2/(3\pi)$, the phase values differ by at least $1$. Continuity and the intermediate value theorem show that $2\pi h([l,2\pi])$ contains an angular interval of width $2\pi$. Such an interval covers the whole unit circle under $\theta\mapsto e^{i\theta}$.

For angular points,

$$
|e^{is}-e^{it}|=2\left|\sin\frac{s-t}{2}\right|\le|s-t|.
$$

Thus the length of $t\mapsto e^{i\omega t}$ on $[0,L]$, for $\omega,L\ge0$, is at most $\omega L$. A uniform partition with $N$ cells has chord sum

$$
2N\left|\sin\frac{\omega L}{2N}\right|\longrightarrow\omega L.
$$

This gives the reverse inequality, also when $\omega L=0$. Taking $(\omega,L)=(1,2\pi)$ and $(2,2\pi)$ proves the two finite lengths.

For the third curve choose decreasing times

$$
\tau_n=\frac1{\pi/2+(n+2)\pi},\qquad
\theta_n=2\pi\tau_n=\frac2{n+5/2}.
$$

They lie in $[0,2\pi]$, and

$$
\Im\gamma_3(\tau_n)=(-1)^n\sin\theta_n,\qquad0\le\theta_n\le\pi/2.
$$

Successive imaginary parts have opposite signs. The chord between them is at least $\sin\theta_n$. Using $\sin\theta\ge2\theta/\pi$ on $[0,\pi/2]$ gives the sufficient bound

$$
\frac1{n+3}\le\pi\,|\gamma_3(\tau_{n+1})-\gamma_3(\tau_n)|.
$$

For each finite list, reverse the decreasing times and insert the two interval endpoints. Its chord sum is bounded by the source length. If that length were finite, all partial sums of these nonnegative chords would be bounded, and the displayed bound would make a shifted harmonic series converge. This is impossible. Hence the length is infinite. The proved equality between source length and variation gives infinite variation as well.

**Lean declarations:** `exercise18_common_range`, `exercise18_gamma1_continuous`, `exercise18_first_length`, `exercise18_gamma2_continuous`, `exercise18_second_length`, `exercise18_endpoint_extension`, `exercise18_endpoint_unique`, `exercise18_printed_endpoint_obstruction`, `exercise18_third_nonrectifiable`, `exercise18_third_infinite_variation`, `exercise18_gamma3_positive`, `exercise18_phase_width`, `linearCircle_length`, `exercise18_sample_im`, `exercise18_harmonic_chord`.

<a id="r06e19"></a>
### 6.19 — Invariance under continuous reparameterization
**Lean source:** [Exercise19.lean](../../Math/Rudin/Chapter06/Exercise19.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $c\le d$, let $\gamma:[a,b]\to\mathbb R^k$ be continuous, and let $\varphi:[c,d]\to[a,b]$ be a continuous bijection with $\varphi(c)=a$. Put $\widetilde\gamma=\gamma\circ\varphi$. Then $\widetilde\gamma$ is continuous, and
1. $\widetilde\gamma$ is an arc if and only if $\gamma$ is an arc, where an arc is a continuous injective map of the parameter interval.
2. $\widetilde\gamma$ is a closed curve if and only if $\gamma$ is a closed curve, where closed means equality of the endpoint values.
3. The curves have equal lengths in $[0,\infty]$, so one is rectifiable if and only if the other is.

The Euclidean norm is the usual $\ell^2$ norm. The file also proves these assertions for a pseudometric target; the length and rectifiability assertions do not require continuity of $\gamma$. Under the full hypotheses, singleton intervals are included. Separately, the length convention gives zero for empty or singleton intervals.

**Proof.** Define the source length by

$$
L(\gamma;[a,b])=\sup_{a=x_0\le\cdots\le x_n=b}
\sum_{i=0}^{n-1}d\bigl(\gamma(x_{i+1}),\gamma(x_i)\bigr),
$$

with the supremum in the extended nonnegative reals. Every partition list is admissible in the definition of variation, so source length is at most variation. Conversely, add $a,b$ to any finite ordered list in $[a,b]$. The extra chords are nonnegative, so its sum is at most a full partition sum. Thus the two suprema agree. Removing repeated nodes does not change a sum, so strictly increasing finite lists give the same supremum. Empty intervals have no partitions and hence supremum zero; singleton chords are all zero. In a normed space the distance is exactly the norm of the chord difference.

A continuous injective real function on an interval is strictly monotone. The condition $\varphi(c)=a$ and the fact that its range is $[a,b]$ force increasing orientation; the singleton case is immediate. Surjectivity and monotonicity then give $\varphi(d)=b$. Mapping an ordered partition through $\varphi$ preserves its order and its chord sum. Conversely, each ordered partition of $[a,b]$ has ordered preimages by bijectivity and increasing order. Therefore the two length suprema are equal, without assuming finiteness. This also proves the equivalence of rectifiability.

Composition gives continuity of $\widetilde\gamma$. Injectivity is preserved in one direction by composition of injections; in the other, lift two parameters of $\gamma$ through the surjection $\varphi$ and use injectivity of the composite. Finally, $\widetilde\gamma(c)=\gamma(a)$ and $\widetilde\gamma(d)=\gamma(b)$ give the closed-curve equivalence.

**Lean declarations:** `exercise19_arc`, `exercise19_closed_curve`, `exercise19_rectifiability`, `exercise19_length`, `exercise19_euclidean`, `curveLength_eq_eVariationOn`, `curveLength_eq_zero_of_ge`, `curveLength_eq_strictLists`, `curveChordSum_eq_norm`, `reparam_strictMono`, `reparam_last`, `reparam_continuous`.

<a id="chapter-07"></a>

## Chapter 7 — Sequences and Series of Functions

**Exercises:** [1](#r07e01) · [2](#r07e02) · [3](#r07e03) · [4](#r07e04) · [5](#r07e05) · [6](#r07e06) · [7](#r07e07) · [8](#r07e08) · [9](#r07e09) · [10](#r07e10) · [11](#r07e11) · [12](#r07e12) · [13](#r07e13) · [14](#r07e14) · [15](#r07e15) · [16](#r07e16) · [17](#r07e17) · [18](#r07e18) · [19](#r07e19) · [20](#r07e20) · [21](#r07e21) · [22](#r07e22) · [23](#r07e23) · [24](#r07e24) · [25](#r07e25) · [26](#r07e26)

Positive series indices below correspond to Lean indices shifted by one where indicated in the source.

<a id="r07e01"></a>
### 7.1 — A common bound for a uniformly convergent sequence
**Lean source:** [Exercise01.lean](../../Math/Rudin/Chapter07/Exercise01.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $E$ be any subset of a set $X$, and let $f_n:X\to V$, where $V$ is a normed additive commutative group. Suppose $f_n\to f$ uniformly on $E$ and, for each $n$, there is a real number $M_n$ such that $\|f_n(x)\|\le M_n$ for every $x\in E$. Then there is one real number $M$ such that $\|f_n(x)\|\le M$ for all $n$ and $x\in E$. This includes real and complex functions and the empty domain.

**Proof.** Choose $N$ such that $\|f_n(x)-f(x)\|<1$ whenever $n\ge N$ and $x\in E$. Taking $n=N$ gives $\|f(x)\|\le M_N+1$, hence $\|f_n(x)\|\le M_N+2$ for $n\ge N$. For the finitely many earlier indices, use their individual bounds. With indices starting at zero, the single choice

$$
M=2+|M_N|+\sum_{i<N}|M_i|
$$

works in both cases. If $E$ is empty, all the required inequalities are vacuous.

**Lean declarations:** `exercise01_uniform_bound`.

<a id="r07e02"></a>
### 7.2 — Uniform limits of sums and products
**Lean source:** [Exercise02.lean](../../Math/Rudin/Chapter07/Exercise02.lean).
**Inventory status:** Verified as stated.

**Statement.** If $f_n\to f$ and $g_n\to g$ uniformly on an arbitrary set $E$, with values in a normed additive commutative group, then $f_n+g_n\to f+g$ uniformly on $E$. If the values lie in a normed ring and each $f_n$ and $g_n$ is bounded on $E$, then $f_ng_n\to fg$ uniformly there. The product result includes real and complex functions; the ring need not be commutative.

**Proof.** The sum estimate is

$$
\|(f+g)-(f_n+g_n)\|\le \|f-f_n\|+\|g-g_n\|.
$$

Make both terms less than $\varepsilon/2$, uniformly on $E$.

For products, Exercise 7.1 gives nonnegative common bounds $A$ and $B$ for $\|f_n\|$ and $\|g_n\|$. Pointwise passage to the limit gives $\|g\|\le B$. The identity

$$
fg-f_ng_n=(f-f_n)g+f_n(g-g_n)
$$

yields

$$
\|fg-f_ng_n\|\le B\|f-f_n\|+A\|g-g_n\|.
$$

Make both errors less than $\delta=\varepsilon/(A+B+1)$. The last expression is at most $(A+B)\delta<\varepsilon$. No initial common bound was assumed.

**Lean declarations:** `exercise02_sums`, `exercise02_products`.

<a id="r07e03"></a>
### 7.3 — Products can fail to converge uniformly
**Lean source:** [Exercise03.lean](../../Math/Rudin/Chapter07/Exercise03.lean).
**Inventory status:** Verified as stated.

**Statement.** On $\mathbb R$, set $f_n(x)=x$ and $g_n(x)=1/(n+1)$ for $n\ge0$. Both sequences converge uniformly, respectively to $x$ and $0$. Their product converges pointwise to zero but has no uniform limit on $\mathbb R$.

**Proof.** The first sequence is constant in $n$. The error for the second is $1/(n+1)$, independent of $x$, and tends to zero. At any fixed $x$, the product $x/(n+1)$ tends to zero. However, at $x=n+1$ the product equals $1$, so its error cannot eventually be less than $1/2$ everywhere. Any uniform limit would also be a pointwise limit and would therefore equal zero. Thus no alternative uniform limit exists.

**Lean declarations:** `exercise03_unbounded_product_example`, `exercise03_first_uniform`, `exercise03_second_uniform`, `exercise03_pointwise`, `exercise03_not_uniform`, `exercise03_no_uniform_limit`.

<a id="r07e04"></a>
### 7.4 — A positive series near a singular parameter
**Lean source:** [Exercise04.lean](../../Math/Rudin/Chapter07/Exercise04.lean).
**Inventory status:** Verified as stated.

**Statement.** For real $x$, consider

$$
S_N(x)=\sum_{n=1}^{N}\frac1{1+n^2x^2}.
$$

The series converges absolutely exactly when $x\ne0$; write its sum as $S(x)$ on that domain. Its partial sums have a uniform limit on a set $E\subseteq\mathbb R$ if and only if

$$
\text{there is }\delta>0\text{ such that }|x|\ge\delta\quad(x\in E).
$$

When this holds, the limit is $S$ on $E$. Consequently, this criterion classifies every interval: the empty interval is allowed, a singleton works exactly when its point is nonzero, and any interval containing or approaching zero fails. The sum is continuous throughout $\mathbb R\setminus\{0\}$ and is unbounded above on that domain.

**Proof.** For $|x|\ge\delta>0$,

$$
0\le\frac1{1+n^2x^2}\le\frac1{\delta^2n^2}.
$$

The convergent reciprocal-square series gives absolute convergence at every nonzero point and uniform convergence on every such $E$ by the Weierstrass test. At zero, $S_N(0)=N$, so there is no finite limit.

Conversely, suppose the partial sums converge uniformly on $E$. Their uniform Cauchy condition, with error $1/2$, gives an index $N$ for which

$$
|S_{N+1}(x)-S_N(x)|<\frac12\qquad(x\in E).
$$

If $(N+1)|x|\le1$, the left side is $1/(1+(N+1)^2x^2)\ge1/2$, a contradiction. Thus $E$ is bounded away from zero. In particular, failure is equivalent to the condition that, for every $\delta>0$, some $x\in E$ has $|x|<\delta$. This also handles empty sets and degenerate intervals without exceptions.

Each term is continuous because its denominator is positive. Near any nonzero $x_0$, restrict to the open neighborhood $|x|>|x_0|/2$; convergence there is uniform. The uniform-limit theorem gives continuity at $x_0$.

Finally, at $x=1/(N+1)$ each of the first $N$ terms is at least $1/2$. Hence

$$
S\left(\frac1{N+1}\right)\ge\frac N2.
$$

Choosing $N>2M$ gives a nonzero point with $S(x)>M$, for any prescribed real $M$.

**Scope.** The Lean expression for the infinite sum is defined at every real number, but it represents the series sum only at nonzero arguments. No value at zero is used to claim convergence or continuity there.

**Lean declarations:** `exercise04_absolute_domain`, `exercise04_pointwise`, `exercise04_zero_partialSum`, `exercise04_zero_diverges`, `exercise04_uniform_iff`, `exercise04_uniform_intervals`, `exercise04_no_uniform_limit_iff`, `exercise04_uniform_empty`, `exercise04_uniform_singleton_iff`, `exercise04_continuousAt`, `exercise04_continuity`, `exercise04_large_value`, `exercise04_unbounded`.

<a id="r07e05"></a>
### 7.5 — Shrinking supports and failure of uniform convergence
**Lean source:** [Exercise05.lean](../../Math/Rudin/Chapter07/Exercise05.lean).
**Inventory status:** Verified as stated.

**Statement.** For $n\ge1$, define on $\mathbb R$

$$
f_n(x)=
\begin{cases}
\sin^2(\pi/x),&1/(n+1)\le x\le1/n,\\
0,&\text{otherwise}.
\end{cases}
$$

Both support endpoints are included. Each $f_n$ is continuous, and $f_n(x)\to0$ at every real point. The limit is continuous, but the sequence has no uniform limit on $\mathbb R$. The series $\sum_{n\ge1}f_n(x)$ converges absolutely at every real $x$, while its ordered partial sums have no uniform limit on $\mathbb R$.

**Proof.** At each support endpoint, $\pi/x$ is an integer multiple of $\pi$, so the interior expression is zero. It therefore joins continuously to the zero function outside the support. In particular, $f_n(0)=0$.

If $x\le0$, every term vanishes. If $x>0$, then eventually $1/n<x$, so every sufficiently late term vanishes. Thus the sequence tends pointwise to the continuous zero function, and each numerical series has only finitely many nonzero terms. This proves absolute convergence as well as ordinary partial-sum convergence.

For every $n\ge1$, the point $x_n=1/(n+1/2)$ lies inside the support and satisfies

$$
f_n(x_n)=\sin^2\bigl((n+1/2)\pi\bigr)=1.
$$

Therefore $f_n$ does not tend uniformly to zero. Pointwise uniqueness excludes any other uniform limit. If the series partial sums were uniformly convergent, their consecutive differences $f_n$ would tend uniformly to zero by the uniform Cauchy condition. The same peak values contradict this, regardless of the proposed limit of the partial sums.

**Lean declarations:** `exercise05_endpoints`, `exercise05_term_continuous`, `exercise05_pointwise_limit`, `exercise05_limit_continuity`, `exercise05_sequence_not_uniform`, `exercise05_sequence_no_uniform_limit`, `exercise05_series_absolute`, `exercise05_series_pointwise`, `exercise05_series_no_uniform_limit`, `exercise05_series_not_uniform`.

<a id="r07e06"></a>
### 7.6 — Locally uniform but nowhere absolute convergence
**Lean source:** [Exercise06.lean](../../Math/Rudin/Chapter07/Exercise06.lean).
**Inventory status:** Verified as stated.

**Statement.** The real series

$$
\sum_{n=1}^{\infty}(-1)^n\frac{x^2+n}{n^2}
$$

converges in its displayed order at every $x\in\mathbb R$, uniformly on every bounded subset of $\mathbb R$. This includes all bounded intervals, empty or degenerate. It converges absolutely at no real point.

**Proof.** Split each term as

$$
(-1)^n\frac{x^2+n}{n^2}=x^2\frac{(-1)^n}{n^2}+\frac{(-1)^n}{n}.
$$

The first coefficient series is absolutely convergent; call its sum $A$. The second has an ordinary ordered limit $b$ by the alternating-series test. On $|x|\le R$, the first subseries has the summable uniform majorant $R^2/n^2$. The second is constant as a function of $x$, so its numerical convergence is uniform on any domain. Adding their partial sums proves uniform convergence to the same function $Ax^2+b$ on every bounded set. Singleton sets give pointwise convergence.

For every real $x$,

$$
\left|(-1)^n\frac{x^2+n}{n^2}\right|=\frac{x^2+n}{n^2}\ge\frac1n.
$$

The harmonic series diverges, so the nonnegative absolute partial sums have no finite limit.

**Scope.** Convergence of the alternating harmonic part means convergence in the natural order, not unconditional summability. The file does not assert uniform convergence on the whole real line.

**Lean declarations:** `exercise06_harmonic_converges`, `exercise06_uniform_on_bounded_sets`, `exercise06_local_uniform`, `exercise06_pointwise`, `exercise06_nowhere_absolute`.

<a id="r07e07"></a>
### 7.7 — Uniform convergence does not preserve derivative limits
**Lean source:** [Exercise07.lean](../../Math/Rudin/Chapter07/Exercise07.lean).
**Inventory status:** Verified as stated.

**Statement.** For $n\ge1$ and $x\in\mathbb R$, let

$$
f_n(x)=\frac{x}{1+nx^2}.
$$

Then $f_n\to f=0$ uniformly on all of $\mathbb R$. Every $f_n$ is differentiable, with

$$
f_n'(x)=\frac{1-nx^2}{(1+nx^2)^2}.
$$

For $x\ne0$, $f_n'(x)\to0=f'(x)$. At zero, every $f_n'(0)=1$, whereas $f'(0)=0$.

**Proof.** The quotient rule applies since $1+nx^2>0$. To bound the functions, use $(\sqrt n\,|x|-1)^2\ge0$, which implies $\sqrt n\,|x|\le1+nx^2$. Thus

$$
|f_n(x)|\le\frac1{\sqrt n}
$$

for all real $x$, proving global uniform convergence. Also $|1-nx^2|\le1+nx^2$, so

$$
|f_n'(x)|\le\frac1{1+nx^2}.
$$

For a fixed nonzero $x$ the right side tends to zero. At $x=0$, direct substitution gives $f_n'(0)=1$ for every $n$. The constant limit function has derivative zero everywhere, establishing both the agreement off zero and the failure at zero.

**Lean declarations:** `exercise07_hasDerivAt`, `exercise07_norm_bound`, `exercise07_uniform_limit`, `exercise07_derivative_nonzero`, `exercise07_derivative_zero`.

<a id="r07e08"></a>
### 7.8 — An absolutely convergent series of step functions
**Lean source:** [Exercise08.lean](../../Math/Rudin/Chapter07/Exercise08.lean).
**Inventory status:** Verified as stated.

**Statement.** Put $I(t)=0$ for $t\le0$ and $I(t)=1$ for $t>0$. Let $p_n$ be distinct points of $(a,b)$, and let $c_n$ be complex coefficients, or vectors in a complete real normed space, such that the ordinary partial sums of $\sum_n\|c_n\|$ have a finite limit. Then

$$
F(x)=\sum_n I(x-p_n)c_n
$$

is a uniformly convergent series on $[a,b]$, in fact on all of $\mathbb R$. It is continuous at every $x\in[a,b]$ unequal to all $p_n$, including endpoints and accumulation points of the jumps.

**Proof.** The $n$th term is $c_n$ when $p_n<x$ and zero otherwise, including when $x=p_n$. Its norm is at most $\|c_n\|$. The Weierstrass test in a complete normed space proves global uniform convergence. Nonnegativity of $\|c_n\|$ identifies its ordinary finite-sum convergence with the summability needed in that test.

Fix $x\ne p_n$ for every $n$. Each individual step function is constant on some neighborhood of $x$, hence continuous at $x$. Every finite partial sum is therefore continuous there. To prove continuity of $F$, approximate it uniformly within $\varepsilon/3$ by one such partial sum, then use continuity of that partial sum to control its change by $\varepsilon/3$. The triangle inequality controls the change in $F$ by $\varepsilon$. No common neighborhood for infinitely many terms is needed, so accumulation points cause no difficulty. This is continuity in the whole real line, not only relative continuity at the endpoints.

**Scope.** The global uniform-convergence theorem permits arbitrary jump points; distinctness and membership in $(a,b)$ are retained in the source-form statements. The piecewise formulation also works in any complete normed additive commutative group, without scalar multiplication.

**Lean declarations:** `exercise08_step_zero`, `exercise08_source_term`, `exercise08_uniform_global`, `exercise08_uniform_series`, `exercise08_continuity_off_jumps`.

<a id="r07e09"></a>
### 7.9 — Limits along moving points and a false converse
**Lean source:** [Exercise09.lean](../../Math/Rudin/Chapter07/Exercise09.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $E$ be a subset of a metric space $X$, and let $f_n:X\to Y$ take values in a metric space $Y$. Suppose each $f_n$ is continuous on $E$ and $f_n\to f$ uniformly on $E$. If $x_n\in E$ and $x_n\to x\in E$, then $f_n(x_n)\to f(x)$. The converse fails even for continuous real functions on $\mathbb R$.

**Proof.** The uniform-limit theorem makes $f$ continuous on $E$, so $f(x_n)\to f(x)$. Moreover,

$$
d\bigl(f_n(x_n),f(x)\bigr)
\le d\bigl(f_n(x_n),f(x_n)\bigr)+d\bigl(f(x_n),f(x)\bigr).
$$

The first term tends to zero by uniform convergence and the second by relative continuity.

For the converse, take $f_n(t)=t/(n+1)$ on $\mathbb R$. Each is continuous. For any convergent real sequence $x_n\to x$, the sequence $x_n$ is bounded, so $x_n/(n+1)\to0$. Thus every required moving-point limit holds with $f=0$. But $f_n(n+1)=1$, which excludes uniform convergence to zero.

**Lean declarations:** `exercise09_moving_points`, `exercise09_counterexample_continuous`, `exercise09_counterexample_moving`, `exercise09_converse`.

<a id="r07e10"></a>
### 7.10 — A series with exactly the rational discontinuities
**Lean source:** [Exercise10.lean](../../Math/Rudin/Chapter07/Exercise10.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $\{t\}=t-\lfloor t\rfloor$ and define the real function

$$
F(x)=\sum_{n=1}^{\infty}\frac{\{nx\}}{n^2}.
$$

The series converges uniformly on $\mathbb R$. Its discontinuities are exactly the rational numbers, including zero and negative rationals. They form a countable dense set. For every $a\le b$, $F$ has a Riemann integral on $[a,b]$, equal to its interval Lebesgue integral.

**Proof.** Since $0\le\{nx\}<1$, the summable majorant $1/n^2$ proves uniform convergence and the bound $|F(x)|\le\sum_{n\ge1}1/n^2$. If $x$ is irrational, $nx$ is not an integer for any positive integer $n$. Every summand is continuous at $x$, and uniform convergence gives continuity there.

For any real $x$, define

$$
L_n(x)=\begin{cases}
1/n^2,&nx\in\mathbb Z,\\
\{nx\}/n^2,&nx\notin\mathbb Z.
\end{cases}
$$

This is the left limit of the $n$th summand at $x$. The same majorant permits passage of the left limit through the sum, giving

$$
\lim_{y\uparrow x}F(y)=\sum_{n\ge1}L_n(x).
$$

For a rational $x=p/q$, with $q\ge1$, each $L_n(x)$ is at least the corresponding summand of $F(x)$, and the inequality is strict for $n=q$: the values are $1/q^2$ and $0$. Both series converge, so the left limit is strictly greater than $F(x)$. Thus $F$ is discontinuous at every rational point.

Countability and density now follow from those properties of $\mathbb Q$. On any closed bounded interval, $F$ is bounded and its discontinuity set has measure zero. The Lebesgue criterion for Riemann integrability gives an actual Darboux integral, and the Riemann–Lebesgue agreement theorem identifies its value with the interval integral. When $a=b$, that integral is zero.

**Lean declarations:** `fractionalSeries_uniform`, `fractionalSeries_continuousAt`, `fractionalSeries_leftLimit`, `fractionalSeries_not_continuousAt_rat`, `exercise10_discontinuities`, `exercise10_countability`, `exercise10_density`, `exercise10_riemann_integrability`.

<a id="r07e11"></a>
### 7.11 — The uniform Dirichlet test
**Lean source:** [Exercise11.lean](../../Math/Rudin/Chapter07/Exercise11.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $E\subseteq X$, let $f_n:X\to V$ take values in a complete real normed space, and let $g_n:X\to\mathbb R$. Assume that there is a real bound $B$ such that

$$
\left\|\sum_{i=0}^{N-1}f_i(x)\right\|\le B
\quad\text{for every }N\text{ and }x\in E,
$$

that $g_n\to0$ uniformly on $E$, and that $g_n(x)$ is nonincreasing in $n$ at each $x\in E$. Then the ordered partial sums of $\sum_{n\ge0}g_n(x)f_n(x)$ converge uniformly on $E$. In particular, $V$ may be $\mathbb C$; the multipliers $g_n$ remain real.

**Proof.** Replace $B$ by $\max(B,0)$. Since each decreasing numerical sequence $g_n(x)$ has limit zero, all its terms are nonnegative. Write $A_N(x)=\sum_{i<N}f_i(x)$. For $m<n$, summation by parts gives

$$
\sum_{i=m}^{n-1}g_i f_i
=g_{n-1}A_n-g_mA_m
+\sum_{i=m}^{n-2}(g_i-g_{i+1})A_{i+1}.
$$

The triangle inequality, $\|A_j\|\le B$, and monotonicity give

$$
\left\|\sum_{i=m}^{n-1}g_i(x)f_i(x)\right\|
\le B\left(g_{n-1}(x)+g_m(x)+\sum_{i=m}^{n-2}(g_i(x)-g_{i+1}(x))\right)
=2B g_m(x).
$$

For a prescribed $\varepsilon>0$, uniform convergence of $g_m$ makes $g_m(x)<\varepsilon/[2(B+1)]$ for all sufficiently large $m$ and all $x\in E$. The tail estimate then gives the uniform Cauchy condition. Completeness yields the pointwise limits, and the uniform Cauchy condition makes convergence to them uniform. An empty $E$ imposes no condition on the chosen limit outside $E$.

**Scope.** The three source conditions are hypotheses. No convergence of $\sum f_n$ is assumed, and the conclusion concerns ordered convergence, not absolute or unconditional summability.

**Lean declarations:** `exercise11_tail_bound`, `exercise11_uniform_dirichlet_bound`, `exercise11_uniform_dirichlet`.

<a id="r07e12"></a>
### 7.12 — Convergence of dominated improper Riemann integrals
**Lean source:** [Exercise12.lean](../../Math/Rudin/Chapter07/Exercise12.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $g:(0,\infty)\to\mathbb R$ and let $f_n:(0,\infty)\to\mathbb R$, or $f_n:(0,\infty)\to\mathbb C$. Suppose $g$ and every $f_n$ are Riemann integrable on each $[a,b]$ with $0<a<b$, that

$$
|f_n(x)|\le g(x)\qquad(n\ge0,\ x>0),
$$

and that $f_n\to f$ uniformly on every compact subset of $(0,\infty)$. In the complex case, $|\cdot|$ denotes the complex norm. Suppose also that the improper Riemann integral of $g$ is finite. Then $f$ is locally Riemann integrable, the improper integrals of every $f_n$ and of $f$ converge absolutely, and

$$
\lim_{n\to\infty}\int_0^\infty f_n(x)\,dx
=\int_0^\infty f(x)\,dx.
$$

Here an improper integral is the sum of two separate limits,

$$
\lim_{a\downarrow0}\int_a^1 h(x)\,dx
+\lim_{b\to\infty}\int_1^b h(x)\,dx,
$$

not a limit in which the two endpoints are coupled. Integrability on singleton intervals is automatic.

**Proof.** Uniform convergence on singleton compact sets gives pointwise convergence. The domination hypothesis implies $g\ge0$ and, on taking limits, $|f|\le g$.

First consider real functions. Local Riemann integrability implies measurability on the positive ray: use the countable cover $[1/(k+1),k+1]$. A nonnegative locally integrable function with finite improper endpoint limits is Lebesgue integrable on $(0,\infty)$. Indeed, its integrals on the increasing truncated intervals are bounded by the two endpoint limits; monotone convergence identifies their finite supremum with its integral on the whole ray. Thus $g$ is integrable. Measurability and domination give absolute Lebesgue integrability of each $f_n$ and of its pointwise limit $f$. The dominated convergence theorem gives convergence of their integrals.

It remains to retain the Riemann conclusions rather than merely Lebesgue conclusions. Fix $0<a\le b$. The approximating functions have proper Riemann integrals and converge uniformly on $[a,b]$. Their integral values converge to the integral of $f$, by dominated convergence on that interval. For any tagged partition, replacing $f$ by a uniformly close $f_n$ changes its tagged sum by at most

$$
(b-a)\sup_{[a,b]}|f-f_n|.
$$

Choose $n$ so that this error and the difference of integral values are each less than $\varepsilon/3$, and choose a partition controlling the tagged sums for $f_n$ within $\varepsilon/3$. The triangle inequality proves proper Riemann integrability of $f$. Absolute values of locally Riemann integrable real functions are again locally Riemann integrable. Absolute Lebesgue integrability, together with these proper Riemann witnesses, then gives both endpoint limits for $f_n$, $f$, $|f_n|$, and $|f|$. Their improper values equal their Lebesgue integrals, so the already proved integral limit is the required improper Riemann limit.

For complex functions, apply the real argument to the real and imaginary parts. Each is bounded in absolute value by $|f_n|\le g$, and each inherits compact uniform convergence. Combining their proper tagged integrals proves proper complex Riemann integrability of the limit. The norm of a locally complex Riemann integrable function is locally real Riemann integrable. Domination gives absolute integrability of the norms; the separate complex endpoint limits follow from integrability. Finally, dominated convergence for the complex integral proves the displayed limit.

**Scope.** Both the real and complex statements are present. Measurability, absolute integrability, and proper Riemann integrability of the limit are derived, not extra hypotheses.

**Lean declarations:** `exercise12_bridges`, `exercise12_improper_existence`, `exercise12_integral_limit`, `exercise12_complex`.

<a id="r07e13"></a>
### 7.13 — Selection for bounded monotone functions
**Lean source:** [Exercise13.lean](../../Math/Rudin/Chapter07/Exercise13.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $f_n:\mathbb R\to\mathbb R$ be nondecreasing in the real argument, with $0\le f_n(x)\le1$ for every $n,x$. There are strictly increasing indices $k_n$ and a nondecreasing function $g:\mathbb R\to[0,1]$ such that $f_{k_n}(x)\to g(x)$ at every real point, including every discontinuity of $g$. If $g$ is continuous, this convergence is uniform on every compact subset of $\mathbb R$.

More generally, any pointwise-convergent sequence of nondecreasing real functions with continuous limit converges locally uniformly; the bound $[0,1]$ is not needed for this last assertion.

**Proof.** The product $[0,1]^{\mathbb R}$ is compact by Tychonoff's theorem, so the sequence has a cluster point $g$ in the pointwise topology. The set of nondecreasing functions is closed in that topology: each inequality $h(x)\le h(y)$ for $x\le y$ is a closed condition. Hence $g$ is nondecreasing and takes values in $[0,1]$.

A monotone real function has at most countably many discontinuities. Let $D$ be their union with $\mathbb Q$. Restriction to $D$ is continuous, and the countable product of real lines is metrizable. The restricted cluster point is therefore the limit of a subsequence with strictly increasing indices $k_n$. This subsequence converges to $g$ at every point of $D$, including all its discontinuities.

At any other point $x$, $g$ is continuous. Choose rationals $p<x<q$ sufficiently near $x$ that $g(p)$ and $g(q)$ are as close to $g(x)$ as needed. Monotonicity gives

$$
f_{k_n}(p)\le f_{k_n}(x)\le f_{k_n}(q).
$$

Convergence at the rational endpoints and continuity of $g$ squeeze the middle term to $g(x)$. This establishes convergence on the whole line, not just at continuity points.

Finally, assume $g$ is continuous and write $h_n=f_{k_n}$. Given $x$ and $\varepsilon>0$, choose $l<x<r$ so close to $x$ that $g(l)$, $g(r)$, and every $g(y)$ for $l<y<r$ differ from $g(x)$ by less than $\varepsilon/3$. Pointwise convergence at $l,r$ eventually gives

$$
g(l)-\varepsilon/3<h_n(l)\le h_n(y)\le h_n(r)<g(r)+\varepsilon/3.
$$

It follows that $|h_n(y)-g(y)|<\varepsilon$ throughout $(l,r)$ for all sufficiently large $n$. This proves local uniform convergence. A finite subcover of any compact set gives one index valid everywhere on that set. This last argument applies to any such pointwise-convergent sequence and uses no monotonicity in the sequence index.

**Lean declarations:** `exercise13_helly_selection`, `exercise13_locally_uniform`, `exercise13_uniform_on_compact`, `exercise13`.

<a id="r07e14"></a>
### 7.14 — A continuous curve onto the square
**Lean source:** [Exercise14.lean](../../Math/Rudin/Chapter07/Exercise14.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $f:\mathbb R\to\mathbb R$ be continuous and $2$-periodic. Assume $0\le f\le1$ everywhere, $f=0$ on $[0,1/3]$, and $f=1$ on $[2/3,1]$. Define

$$
x(t)=\sum_{n=1}^{\infty}2^{-n}f(3^{2n-1}t),\qquad
y(t)=\sum_{n=1}^{\infty}2^{-n}f(3^{2n}t),\qquad \Phi(t)=(x(t),y(t)).
$$

Both series converge uniformly on $\mathbb R$, and $\Phi$ is continuous. If $C$ is the middle-thirds Cantor set, then

$$
\Phi(C)=\Phi([0,1])=[0,1]^2.
$$

**Proof.** Each summand is continuous and has absolute value at most $2^{-n}$. The Weierstrass majorant test gives uniform convergence and continuity. Nonnegativity and $\sum_{n\ge1}2^{-n}=1$ put both coordinates in $[0,1]$ for every real $t$.

Choose binary expansions

$$
u=\sum_{n\ge1}u_n2^{-n},\qquad v=\sum_{n\ge1}v_n2^{-n},\qquad u_n,v_n\in\{0,1\}.
$$

Interlace them by $a_{2n-1}=u_n$, $a_{2n}=v_n$, and set

$$
t=\sum_{j\ge1}\frac{2a_j}{3^{j+1}}.
$$

This ternary expansion has a leading zero and only zero-or-two digits, so $t\in C$. For every $j\ge1$, removing the first $j-1$ nonzero-position digits gives

$$
3^jt=2k+\sum_{r\ge0}\frac{2a_{j+r}}{3^{r+1}}\quad\text{for some integer }k\ge0.
$$

The tail belongs to $[0,1/3]$ if $a_j=0$, and to $[2/3,1]$ if $a_j=1$. Periodicity and the plateau conditions therefore give $f(3^jt)=a_j$. Substitution yields $x(t)=u$ and $y(t)=v$. Closed plateau intervals make this argument valid for endpoint values and either permitted binary expansion. Thus every point of the square has a preimage in $C\subset[0,1]$, proving both image equalities.

**Lean declarations:** `exercise14_continuity`, `exercise14_constructive_cantor`, `exercise14_cantor_surjection`, `exercise14_interval_surjection`.

<a id="r07e15"></a>
### 7.15 — Equicontinuity of positive dilations
**Lean source:** [Exercise15.lean](../../Math/Rudin/Chapter07/Exercise15.lean).
**Inventory status:** Verified as stated.
**Statement.** For any $f:\mathbb R\to\mathbb R$, the family $t\mapsto f(nt)$, $n\ge1$, on $[0,1]$ is equicontinuous if and only if

$$
f(x)=f(0)\qquad(x\ge0).
$$

In particular, under the source assumption that $f$ is continuous on $\mathbb R$, this is the exact restriction. Constancy on the negative half-line does not follow.
**Proof.** Fix $x\ge0$ and $\varepsilon>0$. Equicontinuity at $0$ supplies $\delta>0$ such that $|f(nt)-f(0)|<\varepsilon$ for every positive integer $n$ and every $t\in[0,1]$ with $t<\delta$. Choose $n>x$ and $n>x/\delta$. Then $t=x/n$ is admissible, so $|f(x)-f(0)|<\varepsilon$. Since $\varepsilon$ is arbitrary, $f(x)=f(0)$. Conversely, this identity makes every dilation constant on $[0,1]$, which gives equicontinuity. The continuous function $f(x)=\min(x,0)$ satisfies the restriction but has $f(-1)=-1\ne0=f(0)$. The general equivalence does not require continuity; the continuous classification retains the source hypothesis explicitly.

**Lean declarations:** `exercise15_classification`, `exercise15_continuous_classification`, `exercise15_nonconstant_example`.

<a id="r07e16"></a>
### 7.16 — Pointwise convergence of an equicontinuous sequence
**Lean source:** [Exercise16.lean](../../Math/Rudin/Chapter07/Exercise16.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $K$ be compact and let $f_n:K\to Y$ be equicontinuous. If $f_n(x)\to g(x)$ at every $x\in K$, then $f_n\to g$ uniformly. The Lean result allows any compact topological domain and any uniform-space target, and also gives the restriction-to-a-compact-set formulation, including the empty set.
**Proof.** In a metric target, fix $\varepsilon>0$. Equicontinuity gives, for each $x\in K$, a neighborhood $U_x$ such that $d(f_n(y),f_n(x))<\varepsilon/4$ for all $n$ and $y\in U_x$. Taking pointwise limits gives $d(g(y),g(x))\le\varepsilon/4$. Choose finitely many of these neighborhoods covering $K$. Pointwise convergence at their centers supplies one $N$ such that the center errors are less than $\varepsilon/4$ for $n\ge N$. For $y$ in a chosen neighborhood, the triangle inequality now gives $d(f_n(y),g(y))<\varepsilon$. The uniform-space version is the standard compact-domain theorem that pointwise and uniform convergence agree on equicontinuous families; the same finite-cover proof uses entourages in place of metric balls. Apply it to the compact subspace for the set formulation. On an empty domain all convergence conditions are vacuous.

**Lean declarations:** `exercise16_uniform_convergence`, `exercise16_uniform_convergence_on`.

<a id="r07e17"></a>
### 7.17 — Metric and vector versions of convergence theorems
**Lean source:** [Exercise17.lean](../../Math/Rudin/Chapter07/Exercise17.lean).
**Inventory status:** Verified as stated.
**Statement.** For maps $F_n:X\to Y$ into a metric space, uniform convergence to $f$ means

$$
\forall\varepsilon>0\ \exists N\ \forall n\ge N\ \forall x\in X,\quad d(F_n(x),f(x))<\varepsilon.
$$

For a family $F_i:X\to Y$ between metric spaces, the source's equicontinuity condition is the uniform condition

$$
\forall\varepsilon>0\ \exists\delta>0\ \forall x,y\in X\ \forall i,\quad d(x,y)<\delta\ \Longrightarrow\ d(F_i(x),F_i(y))<\varepsilon.
$$

The file proves the following nine extensions.

1. **Supremum criterion (7.9).** Set $s_n=\sup_{x\in X}d(F_n(x),f(x))$ in $[0,\infty]$, with $\sup\varnothing=0$. Then uniform convergence is equivalent to $s_n\to0$. Infinite early errors are permitted; a separate pointwise-convergence assumption is unnecessary.
2. **Continuity (7.12).** A uniform limit of continuous maps into any metric space is continuous. The domain can be any topological space.
3. **Cauchy criterion (7.8).** If $Y$ is complete, a uniform limit exists exactly when, for every $\varepsilon>0$, some $N$ satisfies $d(F_m(x),F_n(x))<\varepsilon$ for all $m,n\ge N$ and all $x$.
4. **Interchange of limits (7.11).** Suppose $Y$ is complete, $F_n\to f$ uniformly on $S$, $x$ is an accumulation point of $S$, and $F_n(t)\to A_n$ as $t\to x$ through $S\setminus\{x\}$. Then $A_n\to L$ for some $L$, and $f(t)\to L$ through the same set. The file also allows any nontrivial approach filter eventually contained in $S$.
5. **Majorant test (7.10).** In a complete normed additive group, if $\|F_n(x)\|\le M_n$ everywhere and the ordered real partial sums of $\sum M_n$ converge to a finite limit, then $\sum F_n$ converges uniformly to its pointwise sum.
6. **Integration (7.16).** Let $a\le b$, let $\alpha$ be nondecreasing on $[a,b]$, and let $F_n:[a,b]\to\mathbb R^k$ be Riemann–Stieltjes integrable with values $v_n=\int_a^bF_n\,d\alpha$. If $F_n\to f$ uniformly, then $f$ is integrable and $v_n\to\int_a^bf\,d\alpha$. Vector integration is coordinatewise. The integrator need not be continuous.
7. **Differentiation (7.17).** In any real Banach space, suppose $x_0\in[a,b]$, every $F_n$ has a derivative $D_n(x)$ relative to $[a,b]$ at each point of that interval, $F_n(x_0)\to v$, and $D_n\to g$ uniformly. Then $F_n$ converges uniformly on $[a,b]$ to a function $f$ with relative derivative $g$ at every point. For $a<b$ this includes one-sided endpoint derivatives. No continuity of $D_n$ is assumed.
8. **Equicontinuity (7.24).** A uniformly convergent sequence of continuous maps from a compact metric space into any metric space satisfies the uniform equicontinuity condition above.
9. **Selection and boundedness (7.25).** An equicontinuous, pointwise bounded sequence on a compact metric domain, with values in a proper metric space, has a uniformly convergent subsequence with continuous limit. A proper metric space is one whose closed bounded sets are compact. If the target is also a normed additive group, there is one $M$ with $\|F_n(x)\|\le M$ for all $n,x$. These assertions include every Euclidean vector target.

**Proof.** For the supremum criterion, uniform error less than $\varepsilon/2$ bounds $s_n$ by $\varepsilon/2$, while $s_n<\varepsilon$ bounds every pointwise error. This also handles empty domains and infinite initial suprema. For continuity, choose a continuous approximant with uniform error less than $\varepsilon/3$ and use its continuity at the chosen point; the triangle inequality gives continuity of the limit.

For the complete-target Cauchy criterion, the uniform Cauchy condition makes each $F_n(x)$ a Cauchy sequence. Completeness supplies $f(x)$. Pass to the pointwise limit in a uniform $\varepsilon/2$ bound to obtain a uniform error at most $\varepsilon/2<\varepsilon$. Conversely, compare two late terms with their uniform limit. For interchange of limits, the same Cauchy bound passes to the approach limit and gives $d(A_m,A_n)\le\varepsilon/2$ for late $m,n$. Hence $A_n\to L$. Fix a late $n$ and bound

$$
d(f(t),L)\le d(f(t),F_n(t))+d(F_n(t),A_n)+d(A_n,L).
$$

The first and third terms are uniformly small and the middle term tends to zero. A nontrivial approach filter ensures that passing bounds to limits is valid; accumulation supplies precisely this condition in the punctured-neighborhood case.

For the majorant test, if $X$ is nonempty the norm bound forces $M_n\ge0$. Convergence of its ordered partial sums then gives summability. The norm of each vector tail is at most the corresponding scalar tail, so completeness and the uniform Cauchy criterion apply. If $X$ is empty the conclusion is immediate.

For integration, write $D=\alpha(b)-\alpha(a)\ge0$. Actual tagged sums use tags in closed partition cells and the increments $\alpha(x_{i+1})-\alpha(x_i)$, not modified endpoint values. A uniform scalar error $|u-w|\le\delta$ gives

$$
|S(u)-S(w)|\le\delta D,\qquad\left|\int u\,d\alpha-\int w\,d\alpha\right|\le\delta D.
$$

Consequently the integrals of a uniformly convergent scalar sequence are Cauchy. Let their limit be $L$. The limit function is bounded because one approximant is bounded. Choose an approximant uniformly close to it and with integral close to $L$, then a partition whose every tagged refinement approximates that approximant's integral. The triangle inequality for these three errors proves that the limit function has integral $L$. Using tolerances with denominator $D+1$ includes $D=0$ and $a=b$. Apply this scalar argument to each of the finitely many coordinates; coordinatewise convergence is Euclidean convergence.

For differentiation, the mean-value estimate on the convex interval gives

$$
\|(F_m-F_n)(y)-(F_m-F_n)(x)\|\le\sup_{t\in[a,b]}\|D_m(t)-D_n(t)\|\,|y-x|.
$$

Here one can use any common derivative-error bound instead of the displayed supremum. Taking $x=x_0$ proves uniform Cauchy convergence of $F_n$, hence a uniform limit $f$. For fixed $x$, divide the same estimate by $|y-x|$ for $y\ne x$. The difference quotients of $F_n$ are uniformly Cauchy on $[a,b]\setminus\{x\}$, and their pointwise limit is the difference quotient of $f$. Interchange their uniform limit with $y\to x$ to obtain derivative $g(x)$. The argument is relative to the closed interval, so includes its endpoints. When $a=b$, the asserted within-derivative condition is vacuous, not a claim of a uniquely determined ordinary derivative.

For equicontinuity, the sequence together with its uniform limit is compact in the uniform topology. The compact-family result of Exercise 7.19 gives equicontinuity, and compactness of the domain makes it uniform. Finally, the closure of an equicontinuous pointwise bounded family in a proper target is compact by Arzelà–Ascoli, as in Exercise 7.19. Sequential compactness selects strictly increasing indices. In a normed target the compact closure is norm bounded, and point evaluation cannot increase the supremum norm; this gives the common bound.

**Lean declarations:** `exercise17_uniform`, `exercise17_equicontinuous`, `exercise17_uniform_iff`, `exercise17_equicontinuous_iff`, `exercise17_metric_sup_criterion`, `exercise17_metric_continuity`, `exercise17_complete_cauchy`, `exercise17_complete_limit_interchange_filter`, `exercise17_complete_limit_interchange`, `exercise17_vector_majorant`, `exercise17_stieltjes_uniform_limit`, `exercise17_hasVectorRSIntegral`, `exercise17_vector_integration`, `exercise17_vector_differentiation`, `exercise17_vector_equicontinuity`, `exercise17_vector_selection_bound`, `exercise17_vector_selection_subsequence`.

<a id="r07e18"></a>
### 7.18 — Compactness of bounded primitives
**Lean source:** [Exercise18.lean](../../Math/Rudin/Chapter07/Exercise18.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $a\le b$. Suppose $f_n$ are real- or complex-valued Riemann-integrable functions on $[a,b]$, and $|f_n(t)|\le M$ for all $n,t$, where $M\ge0$. Define

$$
F_n(x)=\int_a^x f_n(t)\,dt\qquad(a\le x\le b).
$$

There are strictly increasing indices $k_j$ and a continuous $G$ on $[a,b]$ such that $F_{k_j}\to G$ uniformly. The file constructs the primitive values from integrability on the full interval; it does not assume their existence separately in the final statement.
**Proof.** Splitting a Riemann integral shows existence of every primitive value and, for $x\le y$, gives $F_n(y)-F_n(x)=\int_x^y f_n$. The formal complex estimate bounds the real and imaginary integrals separately, giving the sufficient, though nonsharp, bound

$$
|F_n(y)-F_n(x)|\le2M|y-x|,\qquad |F_n(x)|\le2M(b-a).
$$

Thus the primitives are continuous, equicontinuous, and pointwise bounded on a compact interval. Arzelà–Ascoli gives compact closure in the uniform topology, and sequential compactness gives the required subsequence. Real Darboux-integrable inputs embed into the complex formulation by their zero imaginary component; taking real parts of the primitives and of the uniform limit returns the real result. All integrals here are genuine Riemann integrals. If $a=b$, every primitive is zero and the assertion still holds.

**Lean declarations:** `exercise18_complex_integral_bound`, `exercise18_primitive_lipschitz`, `exercise18_primitive_subsequence`, `exercise18_exists_primitive_subsequence`, `exercise18_real_primitive_subsequence`.

<a id="r07e19"></a>
### 7.19 — Compact subsets of a continuous-function space
**Lean source:** [Exercise19.lean](../../Math/Rudin/Chapter07/Exercise19.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $K$ be a compact metric space. A subset $S\subset C(K)$ is compact in the supremum metric if and only if it is closed in that metric, pointwise bounded, and equicontinuous. Both real and complex functions are included. More generally, the equivalence holds in $C(K,Y)$ for any proper metric target $Y$. Empty domains and empty families are allowed.
**Proof.** A compact subset of a metric space is closed. For each $x\in K$, evaluation $f\mapsto f(x)$ is continuous, so its image of a compact $S$ is compact and therefore bounded. To obtain equicontinuity, cover compact $S$ by finitely many uniform balls of radius $\varepsilon/3$. At a fixed $x$, continuity of their finitely many centers gives one neighborhood on which each center varies by less than $\varepsilon/3$. Every member of $S$ is within $\varepsilon/3$ of a center at both points, so its variation is less than $\varepsilon$. This proves necessity.

Conversely, properness makes the closure of each bounded evaluation image compact. Arzelà–Ascoli then says that an equicontinuous family with these pointwise compact closures has compact closure in the uniform topology on compact $K$. If $S$ is closed, its closure is $S$, giving sufficiency. This argument also proves the compact-closure assertion without assuming $S$ closed. Neither direction needs $S$ or $K$ to be nonempty.

**Lean declarations:** `exercise19_necessity_closed`, `exercise19_necessity_bounded`, `exercise19_necessity_equicontinuous`, `exercise19_compact_closure`, `exercise19_sufficiency`, `exercise19_ascoli_iff`.

<a id="r07e20"></a>
### 7.20 — A continuous function with zero moments
**Lean source:** [Exercise20.lean](../../Math/Rudin/Chapter07/Exercise20.lean).
**Inventory status:** Verified as stated.
**Statement.** If $f$ is continuous on $[0,1]$ and

$$
\int_0^1 f(x)x^n\,dx=0\qquad(n=0,1,2,\ldots),
$$

then $f(x)=0$ for every $x\in[0,1]$. The statement holds for real and complex $f$, with the ordinary Riemann integral.
**Proof.** First take real $f$. Linearity gives $\int_0^1f(x)p(x)\,dx=0$ for every real polynomial $p$. Let $M\ge0$ bound $|f|$ on the interval. Given $\varepsilon>0$, Weierstrass approximation supplies $p$ with $|f-p|<\varepsilon/(M+1)$ everywhere. Hence

$$
\left|\int_0^1 f(x)^2\,dx\right|
=\left|\int_0^1 f(x)(f(x)-p(x))\,dx\right|
\le\frac{M\varepsilon}{M+1}\le\varepsilon.
$$

Thus $\int f^2=0$. A continuous nonnegative function on a nondegenerate compact interval with integral zero is identically zero: a positive value, even at an endpoint, would give a positive lower bound on a one-sided interval of positive length. Applying this to $f^2$ proves the conclusion at every point. The Lean argument identifies the continuous Riemann integrals with interval integrals before these estimates and returns to the Darboux formulation for the conclusion. For complex $f$, the moment conditions give zero moments for both $\operatorname{Re}f$ and $\operatorname{Im}f$. Applying the real result to each component gives $f=0$.

**Lean declarations:** `exercise20_polynomial_moments`, `exercise20_square_zero`, `exercise20_zero_moments`, `exercise20_zero_moments_complex`.

<a id="r07e21"></a>
### 7.21 — Complex polynomials are not dense on the circle
**Lean source:** [Exercise21.lean](../../Math/Rudin/Chapter07/Exercise21.lean).
**Inventory status:** Verified as stated.
**Statement.** On $K=\{z\in\mathbb C:|z|=1\}$, let $A$ be the algebra of restrictions of complex polynomials in $z$ alone. Then $A$ separates points and vanishes at no point, but is not uniformly dense in $C(K,\mathbb C)$. Specifically, the continuous function $h(z)=\overline z$ satisfies

$$
\|p-h\|_\infty\ge1
$$

for every polynomial $p$, and the same lower bound holds for every function in the uniform closure of $A$.
**Proof.** The polynomial $p(z)=z$ separates any two distinct points; the constant polynomial $1$ is nonzero at every point. For an arbitrary polynomial $p$, consider $q(z)=zp(z)-1$. It is holomorphic on a neighborhood of the closed unit disk and $|q(0)|=1$. On its boundary, $z\overline z=1$ and $|z|=1$, so

$$
|q(z)|=|z(p(z)-\overline z)|=|p(z)-\overline z|.
$$

The maximum modulus principle yields $1\le\|p-h\|_\infty$. Since the norm-distance function is continuous, the closed set $\{g:\|g-h\|_\infty\ge1\}$ contains the entire closure of $A$. It does not contain $h$, whose distance from itself is zero. Thus $h$ lies outside that closure. This proof uses the maximum modulus principle rather than the source's suggested integral argument.

**Lean declarations:** `exercise21_mem_iff`, `exercise21_point_separation`, `exercise21_nonvanishing`, `exercise21_uniform_separation`, `exercise21_closure_separation`, `exercise21_not_dense`.

<a id="r07e22"></a>
### 7.22 — Polynomial approximation in Stieltjes mean square
**Lean source:** [Exercise22.lean](../../Math/Rudin/Chapter07/Exercise22.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $a\le b$, let $\alpha$ be nondecreasing on $[a,b]$, and let $f\in\mathcal R(\alpha)$ there. There are polynomials $p_n$, real for real $f$ and complex for complex $f$, such that the actual Riemann–Stieltjes integrals

$$
E_n=\int_a^b|f(x)-p_n(x)|^2\,d\alpha(x)
$$

exist, are nonnegative, and tend to zero. No continuity or right-continuity of $\alpha$, and no positive-mass condition, is imposed.
**Proof.** For real $f$ and $\varepsilon>0$, the continuous-approximation construction of Exercise 6.12 gives a continuous $g$ with

$$
A=\int_a^b(f-g)^2\,d\alpha<\varepsilon/4.
$$

That construction uses a partition with small Darboux gap and its continuous polygon interpolant, so it applies to the original Stieltjes increments even when $\alpha$ has jumps. Put $D=\alpha(b)-\alpha(a)\ge0$ and choose, by Weierstrass approximation, a real polynomial $p$ with

$$
\|g-p\|_\infty<\delta,\qquad \delta=\sqrt{\frac{\varepsilon}{4(D+1)}}.
$$

Continuous functions and polynomials are Stieltjes integrable. Closure of the integrable functions under subtraction and squaring gives all error integrals. Monotonicity of the integral gives

$$
B=\int_a^b(g-p)^2\,d\alpha\le\delta^2D\le\varepsilon/4.
$$

Since $(f-p)^2\le2(f-g)^2+2(g-p)^2$, the error $E$ for $p$ satisfies $0\le E\le2A+2B<\varepsilon$. Choose such a polynomial for $\varepsilon=1/(n+1)$; then $0\le E_n<1/(n+1)$ proves convergence. The denominator $D+1$ covers zero mass, including $a=b$.

For complex $f=u+iv$, apply the real construction to $u$ and $v$, producing real polynomials $p_n,q_n$. The complex polynomial $P_n=p_n+iq_n$ has

$$
|f-P_n|^2=(u-p_n)^2+(v-q_n)^2.
$$

Its error integral is the sum of the two nonnegative errors, hence tends to zero. The file states both tagged-refinement and Darboux versions of the real result; these use closed-cell tags and the unchanged endpoint values of $\alpha$.

**Lean declarations:** `exercise22_approximate_real`, `exercise22_polynomial_l2_real`, `exercise22_polynomial_l2_darboux`, `exercise22ComplexPolynomial_eval`, `exercise22_polynomial_l2_complex`.

<a id="r07e23"></a>
### 7.23 — An explicit polynomial approximation to absolute value
**Lean source:** [Exercise23.lean](../../Math/Rudin/Chapter07/Exercise23.lean).
**Inventory status:** Verified as stated.
**Statement.** Define polynomials by

$$
P_0(x)=0,\qquad P_{n+1}(x)=P_n(x)+\frac{x^2-P_n(x)^2}{2}.
$$

For every integer $n\ge0$ and $|x|\le1$,

$$
0\le P_n(x)\le P_{n+1}(x)\le|x|,
$$

and

$$
|x|-P_n(x)\le |x|\left(1-\frac{|x|}{2}\right)^n<\frac2{n+1}.
$$

Consequently $P_n\to|x|$ uniformly on $[-1,1]$.
**Proof.** Write $u=|x|$. The recurrence gives the exact error identity

$$
u-P_{n+1}=(u-P_n)\left(1-\frac{u+P_n}{2}\right).
$$

Starting at $P_0=0$, suppose $0\le P_n\le u\le1$. Then $x^2-P_n^2\ge0$, so $P_{n+1}\ge P_n\ge0$. Both factors in the error identity are nonnegative, so $P_{n+1}\le u$. This proves the monotone bounds by induction. The second factor is at most $1-u/2$, so a second induction gives $u-P_n\le u(1-u/2)^n$.

Set $r=1-u/2$, so $0<r\le1$. Since $r^j\ge r^n$ for $0\le j\le n$,

$$
(n+1)r^n(1-r)\le(1-r)\sum_{j=0}^n r^j=1-r^{n+1}<1.
$$

Using $u=2(1-r)$ gives the strict bound $ur^n<2/(n+1)$. This remains strict when $u=0$, and includes $n=0$. The nonnegative error is bounded independently of $x$ by $2/(n+1)\to0$, proving uniform convergence, including both interval endpoints.

**Lean declarations:** `exercise23_zero`, `exercise23_succ`, `exercise23Value_succ`, `exercise23_error_identity`, `exercise23_monotone_bounds`, `exercise23_geometric_error`, `exercise23_strict_error`, `exercise23_error_bound`, `exercise23_uniform_absolute_value`.

<a id="r07e24"></a>
### 7.24 — Completion by distance-difference functions
**Lean source:** [Exercise24.lean](../../Math/Rudin/Chapter07/Exercise24.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $X$ be a metric space and fix $a\in X$. For $p\in X$, define the complex-valued function

$$
f_p(x)=d(x,p)-d(x,a).
$$

Then $f_p\in C_b(X,\mathbb C)$ and

$$
|f_p(x)|\le d(a,p),\qquad \|f_p-f_q\|_\infty=d(p,q).
$$

Let $Y$ be the closure of $\{f_p:p\in X\}$ in $C_b(X,\mathbb C)$. Then $Y$ is complete and $p\mapsto f_p$, with codomain restricted to $Y$, is an isometry with dense range. No separability assumption is needed.
**Proof.** The reverse triangle inequality gives $|d(x,p)-d(x,a)|\le d(a,p)$, and the distance functions are continuous. Thus $f_p$ is bounded and continuous. The same inequality gives

$$
|f_p(x)-f_q(x)|=|d(x,p)-d(x,q)|\le d(p,q).
$$

At $x=p$ equality holds. Hence the supremum norm of the difference is exactly $d(p,q)$, proving isometry and injectivity. The space of bounded continuous complex-valued functions is complete in the supremum norm. A closed subspace of a complete metric space is complete, so $Y$ is complete. Every $f_p$ belongs to $Y$, and its image is dense there by the definition of closure. Restricting the codomain leaves the metric equality unchanged. The chosen base point already entails that $X$ is nonempty.

**Lean declarations:** `exercise24_pointwise_bound`, `exercise24_continuous`, `exercise24Embedding_apply`, `exercise24_distance`, `exercise24_norm`, `exercise24_isometry`, `exercise24_completion_isometry`, `exercise24_dense_embedding`, `exercise24_completion`.

<a id="r07e25"></a>
### 7.25 — Euler polygons and their residuals
**Lean source:** [Exercise25.lean](../../Math/Rudin/Chapter07/Exercise25.lean).
**Inventory status:** Verified as stated.
**Statement.** Let $\phi:[0,1]\times\mathbb R\to\mathbb R$ be continuous and bounded, let $c\in\mathbb R$, and choose $M\ge0$ such that $|\phi(t,z)|\le M$ throughout the closed strip. The source asks for a solution of $y'=\phi(t,y)$, $y(0)=c$, by the following construction. For each positive integer $N$, put

$$
t_i=i/N,\qquad z_0=c,\qquad z_{i+1}=z_i+N^{-1}\phi(t_i,z_i).
$$

Let $f_N$ interpolate these nodes affinely on each $[t_i,t_{i+1}]$. Define $\Delta_N(t)=f_N'(t)-\phi(t,f_N(t))$ off the mesh and $\Delta_N(t_i)=0$ at every mesh point, including $0$ and $1$.

The current file contains the polygon construction, its cell derivative formula, the residual integral identity in both interval-integral and Riemann forms, the bounds and Riemann integrability in part (a), equicontinuity in part (b), and the uniform residual limit in part (e):

$$
|f_N'|\le M\ \text{where the derivative exists},\qquad
|\Delta_N|\le2M,\qquad |f_N|\le |c|+M=:M_1,
$$

$$
|f_N(t)-f_N(s)|\le M|t-s|,\qquad
f_N(x)=c+\int_0^x[\phi(t,f_N(t))+\Delta_N(t)]\,dt,
\qquad \Delta_N\longrightarrow0\ \text{uniformly on }[0,1].
$$

There are strictly increasing indices $\sigma:\mathbb N\to\mathbb N$ for which $f_{\sigma(n)+1}\to f$ uniformly on $[0,1]$. The limit satisfies $|f|\le M_1$, the composed fields converge uniformly, and

$$
f(x)=c+\int_0^x\phi(t,f(t))\,dt,\qquad f(0)=c,\qquad f'(x)=\phi(x,f(x)).
$$

The derivatives are relative to $[0,1]$, hence one-sided at its endpoints. The composition-limit result itself allows any index map $\sigma$, provided the stated uniform polygon limit exists.

**Scope.** The file includes the subsequence selection and the resulting existence theorem, not only a theorem conditional on a uniform polygon limit. The shared construction permits values in a real normed vector space; the integral identity assumes completeness, and the compactness and uniform-limit arguments additionally assume a proper target. These assumptions hold for the real target of this exercise. No continuity or boundedness of the field outside the closed strip is required. No uniqueness of the differential-equation solution is asserted.

**Proof.** A formula for the polygon, extended constantly outside $[0,1]$, is

$$
f_N(t)=c+\sum_{i=0}^{N-1}\bigl(\min(t,t_{i+1})-\min(t,t_i)\bigr)\phi(t_i,z_i).
$$

The clipped affine factors are continuous, nonnegative, at most $1/N$, and sum to $t$ on $[0,1]$. At $t_i$, the preceding complete increments sum to $z_i-c$. Thus the formula gives $f_N(t_i)=z_i$ and, on the entire closed cell,

$$
f_N(t)=z_i+(t-t_i)\phi(t_i,z_i).
$$

In its open interior, $f_N'(t)=\phi(t_i,z_i)$. For $s\le t$, every clipped factor has a nonnegative increment, and their increments sum to $t-s$ on $[0,1]$. The triangle inequality therefore gives $|f_N(t)-f_N(s)|\le M(t-s)$. The same estimate holds on the whole real line for the constant extension because the sum of clipped increments is at most $t-s$. This proves equicontinuity and bounds every actual derivative, including a derivative at a mesh point if it exists. Comparing with $f_N(0)=c$ yields $|f_N(t)|\le|c|+Mt\le M_1$ on $[0,1]$.

Define a step velocity $v_N$ to equal $\phi(t_i,z_i)$ on $(t_i,t_{i+1}]$ and zero outside the union of these cells. Off the finite mesh, $\Delta_N=v_N-\phi(t,f_N(t))$, so $|\Delta_N|\le2M$; at the mesh it is zero. The composition $t\mapsto\phi(t,f_N(t))$ is continuous on the interval, and $v_N$ is locally constant off the mesh. Hence the bounded residual is continuous except possibly at finitely many points, and is Riemann integrable. The file explicitly identifies its Darboux integral with its interval integral. Integrating each step-velocity term gives its clipped affine factor, and therefore

$$
\int_0^x v_N(t)\,dt=f_N(x)-c.
$$

The functions $v_N$ and $\phi(t,f_N(t))+\Delta_N(t)$ differ only at finitely many mesh points. Their integrals are equal, proving the residual identity, including $x=0,1$.

For the residual-limit argument, all pairs $(t,f_N(t))$ belong to the compact rectangle $[0,1]\times[-M_1,M_1]$, on which $\phi$ is uniformly continuous. If $t\in(t_i,t_{i+1})$, then

$$
|t-t_i|\le N^{-1},\qquad |f_N(t)-f_N(t_i)|\le M/N.
$$

Thus the product-metric distance between $(t,f_N(t))$ and $(t_i,f_N(t_i))$ is at most $(1+M)/N$, independently of the cell and point. Uniform continuity makes the difference of the two field values tend uniformly to zero. This difference is $\Delta_N(t)$ off the mesh, while the mesh values are already zero. The full sequence, not merely a subsequence, therefore has the claimed uniform residual limit.

On the compact interval $[0,1]$, the common Lipschitz estimate gives equicontinuity and the bound $M_1$ gives pointwise boundedness. Arzelà–Ascoli supplies a subsequence with strictly increasing indices $\sigma(n)$ that converges uniformly to a function $f$. This is the required selection in part (c). Passing its bound to the pointwise limit gives $|f(t)|\le M_1$, and uniform convergence gives continuity of $f$. Both the polygons and their limit stay in the same compact rectangle. Uniform continuity of $\phi$ therefore changes the uniform estimate $|f_{\sigma(n)+1}(t)-f(t)|\to0$ into uniform convergence of $\phi(t,f_{\sigma(n)+1}(t))$ to $\phi(t,f(t))$. Strict increase implies $\sigma(n)\to\infty$, so the corresponding residual subsequence tends uniformly to zero. Their sums thus converge uniformly to the continuous function $g(t)=\phi(t,f(t))$.

Each such sum is integrable by the residual identity, and $g$ is integrable by continuity. A uniform integrand error at most $\delta$ bounds every primitive error on $[0,1]$ by $\delta$. Passing to the limit in the residual identities gives $f(x)=c+\int_0^x g(t)\,dt$ for every $x\in[0,1]$. At $x=0$ this gives $f(0)=c$. The fundamental theorem of calculus for continuous integrands gives derivative $g(x)$ in the interval interior and the corresponding one-sided derivatives at both endpoints. Together with the selected subsequence, these steps construct the required solution. The continuous scalar integrand also has an ordinary Riemann integral, equal to its interval integral. Thus its Riemann integral from $0$ to $x$ is $f(x)-c$, as required.

**Lean declarations:** `node_zero`, `node_succ`, `polygon_continuous`, `polygon_zero`, `polygon_cell`, `polygon_mesh`, `polygon_hasDerivAt`, `polygon_norm_sub_le`, `polygon_bound`, `residual_mesh`, `residual_eq_deriv_sub`, `residual_bound`, `residual_riemann_integrable`, `polygon_lipschitz`, `polygon_deriv_bound`, `polygon_equicontinuous`, `velocity_integral`, `residual_integral_identity`, `residual_riemann_identity`, `field_uniformContinuousOn`, `residual_uniform`, `limit_bound`, `composition_uniform`, `limit_integral_equation`, `limit_solution`, `polygon_subsequence`, `exists_solution`, `exercise25_solution`, `exercise25_riemann_solution`.

<a id="r07e26"></a>
### 7.26 — Vector-valued solutions from Euler polygons
**Lean source:** [Exercise26.lean](../../Math/Rudin/Chapter07/Exercise26.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $k\ge0$ and let $\Phi:[0,1]\times\mathbb R^k\to\mathbb R^k$ be continuous and bounded in the Euclidean norm. For every $c\in\mathbb R^k$, the vector Euler polygons from [Exercise 7.25](#r07e25) have a uniformly convergent subsequence on $[0,1]$. Its continuous limit $f$ satisfies

$$
f(0)=c,\qquad f(x)=c+\int_0^x\Phi(t,f(t))\,dt,
\qquad f'(x)=\Phi(x,f(x)).
$$

The derivative is ordinary for $0<x<1$ and one-sided at both endpoints. The residuals of the full polygon sequence tend uniformly to zero. No Lipschitz condition on $\Phi$, and no uniqueness conclusion, is imposed.

**Proof.** Choose $M\ge0$ with $\|\Phi(t,z)\|\le M$ on the strip; any given bound is nonnegative because it bounds $\|\Phi(0,c)\|$. In the mesh construction $t_i=i/N$, define

$$
z_0=c,\qquad z_{i+1}=z_i+N^{-1}\Phi(t_i,z_i)
$$

and interpolate affinely. The same sum and triangle-inequality arguments as in Exercise 7.25 give

$$
\|f_N(t)\|\le\|c\|+M,
\qquad\|f_N(t)-f_N(s)\|\le M|t-s|.
$$

Finite-dimensional Euclidean space is complete, and its closed bounded sets are compact. The vector form of Arzelà–Ascoli therefore supplies strictly increasing indices and a uniform polygon limit $f$. Continuity of $\Phi$ is uniform on the compact set $[0,1]\times\overline B(0,\|c\|+M)$. The cell estimates $|t-t_i|\le1/N$ and $\|f_N(t)-z_i\|\le M/N$ make the residuals uniformly small. At mesh points their defined value is zero. The same uniform continuity gives convergence of $\Phi(t,f_N(t))$ along the selected subsequence to $\Phi(t,f(t))$, uniformly in $t$.

Pass to the limit in the polygon residual integral identity. The integral error is bounded by the interval length times the uniform integrand error, so the displayed integral equation follows. Its integrand is continuous. The fundamental theorem of calculus gives the equation for the derivative, including the two one-sided endpoint derivatives, and evaluation at zero gives $f(0)=c$. This uses the actual vector Euler construction, not a separate differential-equation existence theorem. If $k=0$, the target has one point and all these conclusions still hold.

**Lean declarations:** `exercise26_vector_existence`, `exercise26_vector_residual`.

<a id="chapter-08"></a>

## Chapter 8 — Some Special Functions

**Exercises:** [1](#r08e01) · [2](#r08e02) · [3](#r08e03) · [4](#r08e04) · [5](#r08e05) · [6](#r08e06) · [7](#r08e07) · [8](#r08e08) · [9](#r08e09) · [10](#r08e10) · [11](#r08e11) · [12](#r08e12) · [13](#r08e13) · [14](#r08e14) · [15](#r08e15) · [16](#r08e16) · [17](#r08e17) · [18](#r08e18) · [19](#r08e19) · [20](#r08e20) · [21](#r08e21) · [22](#r08e22) · [23](#r08e23) · [24](#r08e24) · [25](#r08e25) · [26](#r08e26) · [27](#r08e27) · [28](#r08e28) · [29](#r08e29) · [30](#r08e30) · [31](#r08e31)

<a id="r08e01"></a>
### 8.1 — A smooth function with all derivatives zero at the origin
**Lean source:** [Exercise01.lean](../../Math/Rudin/Chapter08/Exercise01.lean).
**Inventory status:** Verified as stated.

**Statement.** Define the real function

$$
f(x)=\begin{cases}e^{-1/x^2},&x\ne0,\\0,&x=0.\end{cases}
$$

It is smooth on all of $\mathbb R$. Every successive derivative genuinely exists at every real point, and $f^{(n)}(0)=0$ for every integer $n\ge0$. In particular, the derivative of $f^{(n)}$ at zero exists and equals zero for every $n\ge0$.

**Proof.** Use the standard smooth function

$$
G(t)=\begin{cases}e^{-1/t},&t>0,\\0,&t\le0.\end{cases}
$$

The library's smooth-extension theorem gives smoothness of $G$ and the following derivative identity, including at zero: for a real polynomial $P$,

$$
\frac{d}{dt}\bigl(P(1/t)G(t)\bigr)
=Q(1/t)G(t),\qquad Q(u)=u^2\bigl(P(u)-P'(u)\bigr).
$$

At $t=0$, both products are understood as their zero extensions. Starting with $P=1$, repeated application of this identity shows that every derivative of $G$ has this form and vanishes at zero. The zero extensions are justified by the decay of $e^{-1/t}$ faster than every power of $1/t$ as $t\downarrow0$, as used in the smooth-extension theorem.

Now $f(x)=G(x^2)$, which gives exactly the stated piecewise formula and is smooth by composition. For each positive order, the higher chain rule (Faà di Bruno's formula) expresses its derivative at zero as a finite sum whose terms each contain a derivative of $G$ evaluated at $0$. Every such factor is zero. Order zero is $f(0)=G(0)=0$. Smoothness ensures existence of all successive derivatives, so the vanishing formulas do not rely on assigning default values to nonexistent derivatives.

**Lean declarations:** `exercise01_formula`, `exercise01_smooth`, `exercise01_flatness`, `exercise01_all_derivatives`, `exercise01_derivatives_at_zero`.

<a id="r08e02"></a>
### 8.2 — Two different iterated sums
**Lean source:** [Exercise02.lean](../../Math/Rudin/Chapter08/Exercise02.lean).
**Inventory status:** Verified as stated.

**Statement.** For positive integers $i,j$, define

$$
a_{ij}=\begin{cases}
0,&i<j,\\
-1,&i=j,\\
2^{j-i},&i>j.
\end{cases}
$$

Every row and every column has a convergent ordinary sum, but

$$
\sum_{i=1}^{\infty}\left(\sum_{j=1}^{\infty}a_{ij}\right)=-2,
\qquad
\sum_{j=1}^{\infty}\left(\sum_{i=1}^{\infty}a_{ij}\right)=0.
$$

The outer sums also converge in their natural order.

**Proof.** Row $i$ is zero after its diagonal term. Its finite sum is

$$
-1+\sum_{j=1}^{i-1}2^{j-i}
=-1+\sum_{k=1}^{i-1}2^{-k}
=-2^{1-i}.
$$

This includes $i=1$, where the finite sum before the diagonal is empty. Summing the row sums gives the geometric series $-\sum_{i\ge1}2^{1-i}=-2$.

Column $j$ starts with $j-1$ zeros, followed by $-1$ and the geometric tail $2^{-1},2^{-2},\ldots$. Its sum is $-1+\sum_{k\ge1}2^{-k}=0$. Consequently every outer partial sum of the column sums is zero. These calculations establish convergence of every inner sum and both outer sums, while their unequal values show that interchanging the two infinite sums is invalid for this signed array.

**Lean declarations:** `exercise02_formula`, `exercise02_source_formula`, `exercise02_rows`, `exercise02_columns`, `exercise02_row_then_outer`, `exercise02_column_then_outer`.

<a id="r08e03"></a>
### 8.3 — Interchanging nonnegative double sums
**Lean source:** [Exercise03.lean](../../Math/Rudin/Chapter08/Exercise03.lean).
**Inventory status:** Verified as stated.

**Statement.** For an array of nonnegative real numbers $a_{ij}$, indexed by $i,j\ge1$,

$$
\sum_{i=1}^{\infty}\left(\sum_{j=1}^{\infty}a_{ij}\right)
=\sum_{j=1}^{\infty}\left(\sum_{i=1}^{\infty}a_{ij}\right),
$$

where both sides take values in $[0,\infty]$. In particular, one side is infinite if and only if the other is infinite. The result also holds when individual entries themselves may be $+\infty$. The inner sums and the outer sums are limits of their natural ordered partial sums.

**Proof.** Tonelli's theorem for nonnegative series identifies either order of summation with the sum over all pairs $(i,j)$. Equivalently, both sides are the supremum of all finite subsums of the array: any finite set of pairs is contained in a finite rectangle, and nonnegativity makes these subsums increase when indices are added. Thus the two extended values agree without any finiteness assumption.

For each fixed row, the first $N$ terms increase to the supremum of its finite subsums, which is its extended sum. The same applies to the sequence of row sums and, after interchanging the indices, to columns and column sums. This proves the asserted ordered convergence even when the limit is infinite. For finite nonnegative real entries, their embedding into $[0,\infty]$ preserves their values, so the extended theorem applies directly. Equality immediately gives the equivalence of divergence to infinity in the two orders.

**Lean declarations:** `exercise03_nonnegative_interchange`, `exercise03_ordered_sums`, `exercise03_infinite_iff`, `exercise03_real_entries`.

<a id="r08e04"></a>
### 8.4 — Four limits involving powers and logarithms
**Lean source:** [Exercise04.lean](../../Math/Rudin/Chapter08/Exercise04.lean).
**Inventory status:** Verified as stated.

**Statement.** The following real limits hold:

1. For $b>0$,

   $$
   \lim_{x\to0}\frac{b^x-1}{x}=\log b.
   $$

2. On the natural domain $x>-1$,

   $$
   \lim_{x\to0}\frac{\log(1+x)}x=1.
   $$

3. For nonzero $x$ near zero, with $1+x>0$,

   $$
   \lim_{x\to0}(1+x)^{1/x}=e.
   $$

4. For each fixed real $x$,

   $$
   \lim_{n\to\infty}\left(1+\frac xn\right)^n=e^x.
   $$

   Here $n$ runs through positive integers, and the base is positive for all sufficiently large $n$.

The first three limits are punctured, two-sided limits at zero.

**Proof.** The derivative of $b^x$ at zero is $b^0\log b=\log b$, so its difference quotient proves the first limit. The derivative of $\log(1+x)$ at zero is $1$, giving the second. For all sufficiently small $|x|$, $1+x>0$, and hence

$$
(1+x)^{1/x}=\exp\left(\frac{\log(1+x)}x\right).
$$

The second limit and continuity of the exponential give the third.

The fourth assertion is the standard exponential limit for arbitrary fixed real $x$, used directly from the library. It can also be seen from the second limit: if $x\ne0$, put $t_n=x/n$. Then $t_n\to0$ through nonzero values and

$$
n\log(1+x/n)=x\,\frac{\log(1+t_n)}{t_n}\longrightarrow x.
$$

Exponentiation gives the result once $1+x/n>0$. This eventual positivity follows from $x/n\to0$. If $x=0$, every positive-index term is $1=e^0$. No value assigned at the initial index $n=0$ affects the limit.

**Lean declarations:** `exercise04_a`, `exercise04_b`, `exercise04_positive_base`, `exercise04_c`, `exercise04_d`, `exercise04_d_positive_base`.

<a id="r08e05"></a>
### 8.5 — Four limits from exponential and trigonometric remainders
**Lean source:** [Exercise05.lean](../../Math/Rudin/Chapter08/Exercise05.lean).
**Inventory status:** Verified as stated.

**Statement.** With the natural real domains of the expressions,

$$
\begin{aligned}
\text{(a)}\quad&\lim_{x\to0}\frac{e-(1+x)^{1/x}}x=\frac e2,\\
\text{(b)}\quad&\lim_{n\to\infty}\frac n{\log n}\bigl(n^{1/n}-1\bigr)=1\quad(n\in\mathbb N,\ n>1),\\
\text{(c)}\quad&\lim_{x\to0}\frac{\tan x-x}{x(1-\cos x)}=\frac23,\\
\text{(d)}\quad&\lim_{x\to0}\frac{x-\sin x}{\tan x-x}=\frac12.
\end{aligned}
$$

The real limits are two-sided, with zero deleted. The power in (a) has positive base near zero.

**Proof.** L'Hôpital's rule gives

$$
\frac{\log(1+x)-x}{x^2}\longrightarrow-\frac12,
$$

because the quotient of the derivatives is $-1/[2(1+x)]$ for sufficiently small nonzero $x$. Put $h(x)=\log(1+x)/x-1$. Then $h(x)\to0$ and $h(x)/x\to-1/2$. The exponential difference quotient $(e^u-1)/u$, continuously extended to value $1$ at zero, tends to $1$. Therefore

$$
\frac{e-(1+x)^{1/x}}x
=-e\,\frac{e^{h(x)}-1}{h(x)}\,\frac{h(x)}x
\longrightarrow\frac e2,
$$

where the continuous extension makes the identity valid also when $h(x)=0$. For (b), set $u_n=\log n/n$. Then $u_n\to0$ and $u_n>0$ for $n>1$. The expression is $(e^{u_n}-1)/u_n$, whose limit is $1$.

For the trigonometric limits, L'Hôpital's rule and $\sin x/x\to1$ give

$$
C(x)=\frac{1-\cos x}{x^2}\longrightarrow\frac12,
\qquad
S(x)=\frac{x-\sin x}{x^3}\longrightarrow\frac16.
$$

Since $\cos x\to1$,

$$
T(x)=\frac{\tan x-x}{x^3}
=\frac{C(x)-S(x)}{\cos x}\longrightarrow\frac13.
$$

The ratios in (c) and (d) are respectively $T(x)/C(x)$ and $S(x)/T(x)$, giving $2/3$ and $1/2$. These nonzero remainder limits also ensure that the original denominators are nonzero in a sufficiently small deleted neighborhood of zero. Thus no value assigned by totalized division at a singular point enters the argument.

**Lean declarations:** `exercise05_a`, `exercise05_b`, `exercise05_c`, `exercise05_d`, `exercise05_domains`.

<a id="r08e06"></a>
### 8.6 — Continuous solutions of the exponential equation
**Lean source:** [Exercise06.lean](../../Math/Rudin/Chapter08/Exercise06.lean).
**Inventory status:** Verified as stated.

**Statement.** Suppose $f:\mathbb R\to\mathbb R$ is not identically zero and satisfies

$$
f(x)f(y)=f(x+y)\qquad(x,y\in\mathbb R).
$$

If $f$ is differentiable, then $f(x)=e^{cx}$ for some real constant $c$. The same conclusion holds if only continuity is assumed. Conversely, every $f(x)=e^{cx}$ is differentiable, is not identically zero, and satisfies the equation. Even without a regularity assumption, the equation and the nonzero hypothesis imply $f(0)=1$ and $f(x)>0$ everywhere.

**Proof.** Choose $t$ with $f(t)\ne0$. The identity $f(t)f(0)=f(t)$ gives $f(0)=1$. Then $f(x)f(-x)=1$, so $f$ never vanishes. Since

$$
f(x)=f(x/2)^2,
$$

it is positive everywhere. Thus positivity is a conclusion, not an additional hypothesis.

For a continuous solution, define $h(x)=\log f(x)$. Positivity and continuity of $f$ make $h$ continuous, and the equation gives $h(x+y)=h(x)+h(y)$. The standard theorem on continuous additive real functions gives $h(x)=xh(1)$: additivity proves this first on rational arguments, and density of the rationals with continuity extends it to every real argument. With $c=h(1)$, exponentiation gives $f(x)=e^{cx}$. A differentiable solution is continuous, so the first part follows as well.

Conversely, $e^{cx}$ is differentiable and never zero, and $e^{cx}e^{cy}=e^{c(x+y)}$ by the exponential addition law.

**Scope.** “Not identically zero” means that $f(t)\ne0$ for at least one real $t$. The identically zero solution of the functional equation is excluded in both regularity cases.

**Lean declarations:** `exercise06_positive`, `exercise06_a`, `exercise06_b`, `exercise06_converse`.

<a id="r08e07"></a>
### 8.7 — Strict bounds for the sine ratio
**Lean source:** [Exercise07.lean](../../Math/Rudin/Chapter08/Exercise07.lean).
**Inventory status:** Verified as stated.

**Statement.** For every real $x$ with $0<x<\pi/2$,

$$
\frac2\pi<\frac{\sin x}{x}<1.
$$

**Proof.** The strict chord bound for sine on $(0,\pi/2)$ gives $(2/\pi)x<\sin x$. The standard strict inequality $\sin x<x$ holds for $x>0$. Divide both inequalities by the positive number $x$ to obtain the conclusion. The open interval is essential to the stated strict lower bound: at $x=\pi/2$ that bound becomes equality, while the displayed ratio is not defined at zero.

**Lean declarations:** `exercise07_sine_ratio`.

<a id="r08e08"></a>
### 8.8 — A sine bound for integer multiples
**Lean source:** [Exercise08.lean](../../Math/Rudin/Chapter08/Exercise08.lean).
**Inventory status:** Verified as stated.

**Statement.** For every integer $n\ge0$ and every real $x$,

$$
|\sin(nx)|\le n|\sin x|.
$$

The integer restriction cannot be dropped: the inequality fails for $n=1/2$ and $x=\pi$.

**Proof.** For $n=0$, both sides are zero. If the bound holds for $n$, the addition formula and $|\cos t|\le1$ give

$$
\begin{aligned}
|\sin((n+1)x)|
&\le |\sin(nx)|\,|\cos x|+|\cos(nx)|\,|\sin x|\\
&\le |\sin(nx)|+|\sin x|\\
&\le(n+1)|\sin x|.
\end{aligned}
$$

Induction proves the assertion for all nonnegative integers. For the stated noninteger example, $|\sin(\pi/2)|=1$, while $(1/2)|\sin\pi|=0$, so the proposed inequality is strictly reversed.

**Lean declarations:** `exercise08_integer_bound`, `exercise08_noninteger_failure`.

<a id="r08e09"></a>
### 8.9 — Harmonic sums and the decimal scale for exceeding one hundred
**Lean source:** [Exercise09.lean](../../Math/Rudin/Chapter08/Exercise09.lean).
**Inventory status:** Verified as stated.

**Statement.** For $N\ge1$, let $H_N=\sum_{j=1}^N1/j$. Then $H_N-\log N$ has a finite limit, the Euler–Mascheroni constant $\gamma$. For a nonnegative integer $m$, $H_{10^m}>100$ holds exactly when $m\ge44$. In particular, the requested decimal scale is located by

$$
H_{10^{43}}<100<H_{10^{44}}.
$$

**Proof.** The standard harmonic-sum theorem gives

$$
H_N-\log N\longrightarrow\gamma.
$$

For the numerical scale, use the library bounds

$$
2.3025850926<\log10<2.3025850934.
$$

The sequence $H_N-\log N$ is decreasing for positive $N$, and its value at $N=6$ is less than $2/3$. Consequently,

$$
H_{10^{43}}<43\log10+\frac23
<43(2.3025850934)+\frac23<100.
$$

In the other direction, the harmonic integral bound $\log(N+1)\le H_N$ and monotonicity of logarithm give

$$
H_{10^{44}}\ge\log(10^{44}+1)\ge44\log10
>44(2.3025850926)>100.
$$

Thus the two bounds are strict and use explicit certified logarithm estimates, rather than an unquantified asymptotic approximation. Since every harmonic summand is positive, $H_N$ increases with $N$. If $m\le43$, then $H_{10^m}\le H_{10^{43}}<100$; if $m\ge44$, then $H_{10^m}\ge H_{10^{44}}>100$. This proves the exact integer-exponent threshold.

**Lean declarations:** `exercise09_sum_eq_harmonic`, `exercise09_a`, `exercise09_b`, `exercise09_decimal_threshold`.

<a id="r08e10"></a>
### 8.10 — Divergence of the prime reciprocal series
**Lean source:** [Exercise10.lean](../../Math/Rudin/Chapter08/Exercise10.lean).
**Inventory status:** Verified as stated.

**Statement.** Define the ordered prime reciprocal partial sums by

$$
P_N=\sum_{\substack{p<N\\p\text{ prime}}}\frac1p.
$$

Then $P_N\to+\infty$. In particular, for every real $M$ there is an $N$ such that $P_N>M$.

**Proof.** Use the standard divergence theorem for prime reciprocals, supplied by the library: the nonnegative sequence

$$
a_n=\begin{cases}1/n,&n\text{ prime},\\0,&\text{otherwise}\end{cases}
$$

is not summable. The values at $0$ and $1$ are zero, so no reciprocal of zero is involved in the prime sum. Its ordinary partial sums equal $P_N$.

For a nonnegative sequence, these partial sums are nondecreasing. If they were bounded above, monotone convergence would give a finite limit and hence summability, contrary to the cited theorem. Therefore they are unbounded above. Monotonicity then gives divergence to $+\infty$: after a partial sum exceeds any fixed $M$, every later one also exceeds $M$.

**Scope.** The file uses the library's prime-reciprocal divergence theorem rather than proving the book's finite-product hint as a separate result. It explicitly converts that theorem into divergence of the ordered prime partial sums and their unboundedness.

**Lean declarations:** `exercise10_partial_eq`, `exercise10_prime_reciprocals`, `exercise10_unbounded`.

<a id="r08e11"></a>
### 8.11 — An Abelian limit for a Laplace integral
**Lean source:** [Exercise11.lean](../../Math/Rudin/Chapter08/Exercise11.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $f:[0,\infty)\to\mathbb C$ be Riemann integrable on $[0,A]$ for every finite $A>0$, and suppose $f(x)\to1$ as $x\to\infty$. For every $t>0$, the improper integral

$$
L(t)=\lim_{A\to\infty}\int_0^A e^{-tx}f(x)\,dx
$$

exists and converges absolutely. Moreover,

$$
\lim_{t\downarrow0}tL(t)=1.
$$

Real functions are included by their embedding into $\mathbb C$.

**Proof.** Convergence to one bounds $|f(x)|$ by $2$ for all sufficiently large $x$. On the remaining compact interval, Riemann integrability supplies a finite bound. Thus there is one $M\ge0$ with $|f(x)|\le M$ for every $x\ge0$.

The finite Riemann integrals agree with their interval Lebesgue integrals: apply the real comparison theorem to the real and imaginary components. The countable cover $(0,\infty)=\bigcup_{n\ge0}(0,n+1]$ then supplies almost-everywhere strong measurability on the positive ray. For each $t>0$,

$$
|e^{-tx}f(x)|\le Me^{-tx},\qquad
\int_0^\infty Me^{-tx}\,dx=\frac Mt<\infty.
$$

Hence the Laplace integrand is absolutely integrable. It is also properly Riemann integrable on each finite interval, by multiplication with the continuous exponential. Its finite-interval integrals therefore tend to its integral over $(0,\infty)$, proving the asserted improper-integral interpretation rather than using a default value of a nonintegrable function.

For $t>0$, substitute $y=tx$ to obtain

$$
tL(t)=\int_0^\infty e^{-y}f(y/t)\,dy.
$$

For each fixed $y>0$, $y/t\to\infty$ as $t\downarrow0$, so the integrand tends to $e^{-y}$. Its norm is at most $Me^{-y}$, independently of $t$, and this majorant is integrable. The dominated convergence theorem gives

$$
\lim_{t\downarrow0}tL(t)=\int_0^\infty e^{-y}\,dy=1.
$$

The point $y=0$ has measure zero and requires no limit assumption on $f(0)$.

**Lean declarations:** `complex_riemann_bridge`, `exercise11_truncated_riemann`, `exercise11_measurable`, `exercise11_bounded`, `exercise11_laplace_integrable`, `exercise11_improper_integral`, `exercise11_change_variable`, `exercise11_abelian_limit`.

<a id="r08e12"></a>
### 8.12 — The periodic indicator, sine series, and the sinc-square integral

**Lean source:** [Exercise12.lean](../../Math/Rudin/Chapter08/Exercise12.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $0<\delta<\pi$. Let $f_\delta$ be the $2\pi$-periodic function whose values on $[-\pi,\pi]$ are $1$ when $|x|\le\delta$ and $0$ otherwise. In particular, both endpoints have value zero, while $f_\delta(\pm\delta)=1$. With the convention

$$
c_n=\frac{1}{2\pi}\int_{-\pi}^{\pi}e^{-inx}f_\delta(x)\,dx,
$$

all its complex Fourier coefficients are

$$
c_0=\frac{\delta}{\pi},\qquad c_n=\frac{\sin(n\delta)}{n\pi}\quad(n\in\mathbb Z\setminus\{0\}).
$$

The following series converge in their usual order:

$$
\sum_{n=1}^{\infty}\frac{\sin(n\delta)}{n}=\frac{\pi-\delta}{2},\qquad
\sum_{n=1}^{\infty}\frac{\sin^2(n\delta)}{n^2\delta}=\frac{\pi-\delta}{2}.
$$

The second assertion also includes summability as a nonnegative family. Define $\operatorname{sinc}(x)=\sin x/x$ for $x\ne0$ and $\operatorname{sinc}(0)=1$. Its square is integrable on $[0,\infty)$, and

$$
\int_0^\infty\operatorname{sinc}^2(x)\,dx=\frac{\pi}{2},\qquad
\lim_{A\to\infty}\int_0^A\operatorname{sinc}^2(x)\,dx=\frac{\pi}{2}.
$$

For each $A\ge0$, the tagged Riemann integral on $[0,A]$ exists and equals the corresponding finite interval integral above. This includes the zero-length interval. The continuous value of the integrand at zero is $1$. Finally,

$$
\sum_{n=0}^{\infty}\frac{1}{(2n+1)^2}=\frac{\pi^2}{8},
$$

both as a summable family and as a limit of the ordered partial sums.

**Proof.** First put $g_\delta=\mathbf1_{[-\delta,\delta]}$ on the real line. The periodic function is constructed by choosing the representative in $(-\pi,\pi]$ modulo $2\pi$. Periodicity holds for every real $\delta$. If $\delta<\pi$, this construction agrees with $g_\delta$ on the entire closed interval $[-\pi,\pi]$: at $-\pi$ the chosen representative is $\pi$, and both indicator values are zero. Thus its Fourier coefficients equal those of the indicator on this interval.

The source also checks ordinary Riemann integrability, not only measurable integrability. For every $\delta\ge0$, write

$$
g_\delta(x)=\mathbf1_{\{x\le\delta\}}-\mathbf1_{\{x<-\delta\}}.
$$

Both real functions on the right are decreasing, so each has a tagged Riemann integral on $[-\pi,\pi]$. Their difference is the real part of $g_\delta$, and its imaginary part is zero. This proves complex Riemann integrability, including $\delta=0$ and $\delta\ge\pi$. Agreement on the closed interval then proves Riemann integrability of the periodic function for $0\le\delta<\pi$. The identities claimed above retain the strict assumptions $0<\delta<\pi$.

For these strict assumptions, the coefficient integral restricts to $[-\delta,\delta]$. At $n=0$ it is $2\delta/(2\pi)$. For every nonzero integer $n$, integration of the exponential gives

$$
c_n=\frac{1}{2\pi}\left[\frac{e^{-inx}}{-in}\right]_{-\delta}^{\delta}
=\frac{\sin(n\delta)}{n\pi}.
$$

This includes negative frequencies; in particular, $c_{-n}=c_n$. The indicator is measurable and bounded in norm by $1$, so it belongs to $L^2$ on the finite fundamental interval for every real $\delta$. Under $0<\delta<\pi$, its normalized squared norm is

$$
\frac{1}{2\pi}\int_{-\pi}^{\pi}|g_\delta(x)|^2\,dx=\frac{\delta}{\pi}.
$$

Parseval, with this normalization, therefore gives a summable family indexed by $\mathbb Z$ and the equality

$$
\frac{\delta}{\pi}=\frac{\delta^2}{\pi^2}
+\frac{2}{\pi^2}\sum_{n=1}^{\infty}\frac{\sin^2(n\delta)}{n^2}.
$$

Separate the zero coefficient, pair positive and negative frequencies, and multiply by $\pi^2/(2\delta)$. This proves the sine-square identity and hence its ordered partial-sum limit. No reciprocal-square evaluation is used in this argument.

To prove the unsquared sine identity, let $s_N$ be the symmetric Fourier partial sum of $f_\delta$ at zero. The coefficient formulas give, also for $N=0$,

$$
s_N=\frac{\delta}{\pi}+\frac{2}{\pi}\sum_{n=1}^{N}\frac{\sin(n\delta)}{n}.
$$

The periodic function equals $1$ in a neighborhood of zero. Its two one-sided limits there are thus $1$. Pointwise Fejer convergence for periodic Riemann-integrable functions, as proved in Exercise 8.16, shows that the arithmetic means of $s_0,\ldots,s_N$ tend to $1$. Moreover, for each $k\ge1$,

$$
|k(s_k-s_{k-1})|=\frac{2}{\pi}|\sin(k\delta)|\le\frac{2}{\pi}.
$$

The Tauberian converse proved in Exercise 3.14(e) applies to this bounded sequence of weighted differences and the convergent arithmetic means. It yields $s_N\to1$. Solving the displayed formula for the sine partial sum gives the claimed ordered limit. This argument does not assert absolute summability of the unsquared sine series.

For the improper integral, the proof makes the passage from the sine-square sum to an integral explicit. For any mesh $\delta>0$ and $x\ge0$, define the right-endpoint sample

$$
q_\delta(x)=\delta\bigl(\lfloor x/\delta\rfloor+1\bigr).
$$

It is measurable and satisfies $x<q_\delta(x)\le x+\delta$. The intervals $[n\delta,(n+1)\delta)$, $n\ge0$, are pairwise disjoint and cover $[0,\infty)$. On the $n$th interval the sample equals $(n+1)\delta$, so

$$
\int_0^\infty\operatorname{sinc}^2(q_\delta(x))\,dx
=\sum_{n=0}^{\infty}\delta\operatorname{sinc}^2((n+1)\delta).
$$

Here both integrability and summability are proved. The common integrable bound is

$$
0\le\operatorname{sinc}^2(y)\le\frac{4}{(x+1)^2}
\quad(0\le x\le y,\ y>0).
$$

For $x\le1$, use $|\operatorname{sinc}(y)|\le1$ and $(x+1)^2\le4$. For $x>1$, use $(x+1)^2\le4y^2$ and $y^2\operatorname{sinc}^2(y)=\sin^2 y\le1$. The bound is integrable on $[0,\infty)$ by the standard power-integrability criterion. It controls every sampled function and, away from the single point zero, $\operatorname{sinc}^2(x)$ itself. Continuity supplies the value at zero.

When $0<\delta<\pi$, the terms in the sample sum satisfy

$$
\delta\operatorname{sinc}^2((n+1)\delta)
=\frac{\sin^2((n+1)\delta)}{(n+1)^2\delta}.
$$

The sine-square identity therefore evaluates the sampled integral as $(\pi-\delta)/2$. Now take $\delta_j=1/(j+1)$. Each mesh is less than $\pi$, and the sample bounds show $q_{\delta_j}(x)\to x$ for every $x\ge0$, including $x=0$. Continuity of sinc and dominated convergence give convergence of the sampled integrals to the integral of $\operatorname{sinc}^2$. Their known values tend to $\pi/2$. This evaluates the half-line integral. Integrability then gives convergence of the finite interval integrals to the same value as $A\to\infty$. On every $[0,A]$ with $A\ge0$, continuity and the tagged-integral bridge identify the finite integral with the ordinary Riemann integral.

Finally, set $\delta=\pi/2$ in the sine-square identity and multiply by $\pi/2$. The resulting series $\sum_{n\ge1}\sin^2(n\pi/2)/n^2$ has sum $\pi^2/8$. Its even terms vanish, and its odd terms are $1/(2n+1)^2$, since $\sin^2((2n+1)\pi/2)=1$. Splitting the summable family into even and odd indices proves the last identity and its ordered version.

**Lean declarations:** Definitions: `Rudin.Chapter08.exercise12Indicator`, `Rudin.Chapter08.exercise12Periodic`, `Rudin.Chapter08.exercise12Sample`. Coefficients and integrability: `Rudin.Chapter08.exercise12_integral_restrict`, `Rudin.Chapter08.exercise12_coefficient_zero`, `Rudin.Chapter08.exercise12_coefficient`, `Rudin.Chapter08.exercise12_memLp`, `Rudin.Chapter08.exercise12_energy`, `Rudin.Chapter08.exercise12_coeff_norm`, `Rudin.Chapter08.exercise12_riemann`, `Rudin.Chapter08.exercise12_periodic`, `Rudin.Chapter08.exercise12_periodic_eq`, `Rudin.Chapter08.exercise12_periodic_riemann`, `Rudin.Chapter08.exercise12_periodic_coefficient`. Series: `Rudin.Chapter08.exercise12_parseval`, `Rudin.Chapter08.exercise12_sine_square_sum`, `Rudin.Chapter08.exercise12_ordered_sine_square_sum`, `Rudin.Chapter08.exercise12_limit_at_zero`, `Rudin.Chapter08.exercise12_partial_zero`, `Rudin.Chapter08.exercise12_sine_series`, `Rudin.Chapter08.exercise12_odd_square_sum`, `Rudin.Chapter08.exercise12_ordered_odd_square_sum`. Integral: `Rudin.Chapter08.exercise12_sample_bounds`, `Rudin.Chapter08.exercise12_sample_measurable`, `Rudin.Chapter08.exercise12_sinc_dominant`, `Rudin.Chapter08.exercise12_dominant_integrable`, `Rudin.Chapter08.exercise12_steps_integrable`, `Rudin.Chapter08.exercise12_cells_cover`, `Rudin.Chapter08.exercise12_cells_disjoint`, `Rudin.Chapter08.exercise12_cell_integral`, `Rudin.Chapter08.exercise12_riemann_sum_hasSum`, `Rudin.Chapter08.exercise12_sinc_sq_integrable`, `Rudin.Chapter08.exercise12_sample_limit`, `Rudin.Chapter08.exercise12_step_integrals_limit`, `Rudin.Chapter08.exercise12_step_integral`, `Rudin.Chapter08.exercise12_sinc_square_integral`, `Rudin.Chapter08.exercise12_sinc_square_improper`, `Rudin.Chapter08.exercise12_sinc_square_at_zero`, `Rudin.Chapter08.exercise12_sinc_square_riemann`.

<a id="r08e13"></a>
### 8.13 — Parseval for the sawtooth and the reciprocal-square sum

**Lean source:** [Exercise13.lean](../../Math/Rudin/Chapter08/Exercise13.lean).

**Inventory status:** Verified as stated.

**Statement.** Define the sawtooth on $\mathbb R/(2\pi\mathbb Z)$ by taking the representative $x\in[0,2\pi)$ and assigning it the complex value $x$. Its periodic real-line representative has value zero at every multiple of $2\pi$, including $2\pi$ itself. Its Fourier coefficients, with the normalization

$$
c_n=\frac{1}{2\pi}\int_0^{2\pi}x e^{-inx}\,dx,
$$

are

$$
c_0=\pi,\qquad c_n=\frac{i}{n}\quad(n\in\mathbb Z\setminus\{0\}).
$$

The representative $x\mapsto x$ belongs to $L^2$ on $(0,2\pi]$, its normalized energy is $4\pi^2/3$, and Parseval gives

$$
\sum_{n\in\mathbb Z}|c_n|^2=\frac{4\pi^2}{3}.
$$

Consequently,

$$
\sum_{n=1}^{\infty}\frac{1}{n^2}=\frac{\pi^2}{6}.
$$

Both summability and convergence of the ordered partial sums to this value are proved.

**Proof.** The circle construction agrees with $x\mapsto x$ for every $0\le x<2\pi$. The standard coefficient formula for a lifted half-open representative identifies its circle coefficients with the displayed interval integrals. The different assigned value at $2\pi$ does not change any integral.

For the zero coefficient, integration gives

$$
c_0=\frac{1}{2\pi}\left[\frac{x^2}{2}\right]_0^{2\pi}=\pi.
$$

For a nonzero integer $n$, the constant function $1$ has coefficient zero at frequency $n$ by orthogonality of Fourier characters. Apply the interval Fourier differentiation formula to $x\mapsto x$, whose derivative is the integrable constant $1$. Equivalently, integration by parts gives

$$
\int_0^{2\pi}x e^{-inx}\,dx
=\left[\frac{x e^{-inx}}{-in}\right]_0^{2\pi}
+\frac{1}{in}\int_0^{2\pi}e^{-inx}\,dx
=\frac{2\pi i}{n},
$$

because $e^{-2\pi in}=1$ and the last integral is zero. Division by $2\pi$ yields $c_n=i/n$, including negative $n$.

On $(0,2\pi]$, the representative is measurable and its norm is at most $2\pi$. This proves the actual $L^2$ hypothesis needed for interval Parseval. Since $|x|^2=x^2$,

$$
\frac{1}{2\pi}\int_0^{2\pi}x^2\,dx
=\frac{1}{2\pi}\left[\frac{x^3}{3}\right]_0^{2\pi}
=\frac{4\pi^2}{3}.
$$

Apply Parseval with this energy. The zero mode contributes $\pi^2$, and each nonzero mode has squared norm $1/n^2$. Splitting off zero and pairing positive with negative frequencies gives

$$
\frac{4\pi^2}{3}=\pi^2+2\sum_{n=1}^{\infty}\frac{1}{n^2}.
$$

Subtract $\pi^2$ and divide by $2$. Parseval supplies summability before this regrouping, so it proves the reciprocal-square identity without a precomputed zeta value. The ordered partial-sum limit follows from summability.

**Lean declarations:** Definition: `Rudin.Chapter08.exercise13Sawtooth`. Results: `Rudin.Chapter08.exercise13_periodic_value`, `Rudin.Chapter08.exercise13_periodic_coefficient`, `Rudin.Chapter08.exercise13_coefficient_zero`, `Rudin.Chapter08.exercise13_coefficient`, `Rudin.Chapter08.exercise13_memLp`, `Rudin.Chapter08.exercise13_energy`, `Rudin.Chapter08.exercise13_parseval`, `Rudin.Chapter08.exercise13_coeff_norm`, `Rudin.Chapter08.exercise13_square_sum`, `Rudin.Chapter08.exercise13_ordered_square_sum`.

<a id="r08e14"></a>
### 8.14 — A quadratic cosine expansion and two power sums

**Lean source:** [Exercise14.lean](../../Math/Rudin/Chapter08/Exercise14.lean).

**Inventory status:** Verified as stated.

**Statement.** For every $x\in[-\pi,\pi]$, including both endpoints,

$$
(\pi-|x|)^2=\frac{\pi^2}{3}+4\sum_{n=1}^{\infty}\frac{\cos(nx)}{n^2}.
$$

The series is absolutely convergent. Moreover,

$$
\sum_{n=1}^{\infty}\frac1{n^2}=\frac{\pi^2}{6},\qquad
\sum_{n=1}^{\infty}\frac1{n^4}=\frac{\pi^4}{90}.
$$

All three identities also hold as limits of the indicated finite sums.

**Proof.** Apply the library's Bernoulli-polynomial cosine-series identity with index $1$ and coordinate $y=|x|/(2\pi)$. Here $0\le y\le1/2$, and evenness of cosine gives $\cos(2\pi ny)=\cos(nx)$. Substitution of $B_2(y)=y^2-y+1/6$ gives the displayed expansion. The zero-frequency term of the totalized natural-index series is zero; removing it gives exactly the positive-frequency series above. Absolute convergence also follows from $|\cos(nx)|\le1$ and convergence of the reciprocal-square series. Setting $x=0$ and dividing by $4$ gives its sum.

For the fourth powers, represent the same periodic function by $q(t)=(t-\pi)^2$ on $[0,2\pi]$. On negative inputs in $[-\pi,0)$, adding $2\pi$ gives $q(x+2\pi)=(\pi-|x|)^2$; the nonnegative half and both endpoints agree as well. Its complex Fourier coefficients, with normalization $c_n=(2\pi)^{-1}\int_0^{2\pi}q(t)e^{-int}\,dt$, are

$$
c_0=\frac{\pi^2}{3},\qquad c_n=\frac{2}{n^2}\quad(n\ne0).
$$

Integration by parts first gives coefficient $i/n$ for $t-\pi$ and then the stated coefficient for $q$; the endpoint values of $q$ agree. Direct integration gives $(2\pi)^{-1}\int_0^{2\pi}|q|^2=\pi^4/5$. The bounded continuous function $q$ is square integrable, so Parseval yields

$$
\frac{\pi^4}{5}=\frac{\pi^4}{9}+8\sum_{n=1}^{\infty}\frac1{n^4}.
$$

Solving gives $\pi^4/90$. Convergence of the ordered finite sums follows from the proved series sums.

**Lean declarations:** `Rudin.Chapter08.exercise14_frequency`, `Rudin.Chapter08.exercise14_cosine_hasSum`, `Rudin.Chapter08.exercise14_fourier_expansion`, `Rudin.Chapter08.exercise14_ordered_fourier`, `Rudin.Chapter08.exercise14_square_sum`, `Rudin.Chapter08.exercise14_ordered_square_sum`, `Rudin.Chapter08.exercise14_periodic_value`, `Rudin.Chapter08.exercise14_periodic_coefficient`, `Rudin.Chapter08.exercise14_coefficient_zero`, `Rudin.Chapter08.exercise14_coefficient`, `Rudin.Chapter08.exercise14_energy`, `Rudin.Chapter08.exercise14_parseval`, `Rudin.Chapter08.exercise14_fourth_power_sum`, `Rudin.Chapter08.exercise14_ordered_fourth_power_sum`.

<a id="r08e15"></a>
### 8.15 — Fejer kernels and uniform convergence

**Lean source:** [Exercise15.lean](../../Math/Rudin/Chapter08/Exercise15.lean).

**Inventory status:** Verified as stated.

**Statement.** Use the Fourier conventions

$$
c_n(f)=\frac1{2\pi}\int_{-\pi}^{\pi}e^{-int}f(t)\,dt,\qquad
s_N(f;x)=\sum_{n=-N}^{N}c_n(f)e^{inx}.
$$

For $N\ge0$, put $D_N(t)=\sum_{n=-N}^{N}e^{int}=1+2\sum_{k=1}^{N}\cos(kt)$ and $K_N=(N+1)^{-1}\sum_{n=0}^{N}D_n$. Then $K_N$ is continuous, even, and nonnegative, and

$$
K_N(t)=\frac{1-\cos((N+1)t)}{(N+1)(1-\cos t)}\quad(t\notin2\pi\mathbb Z),\qquad
K_N(2\pi k)=N+1.
$$

It satisfies $(2\pi)^{-1}\int_{-\pi}^{\pi}K_N(t)\,dt=1$. If $0<\delta\le|t|\le\pi$, then

$$
K_N(t)\le\frac{2}{(N+1)(1-\cos\delta)}.
$$

For every complex-valued, $2\pi$-periodic function $f$ that is Riemann integrable on $[-\pi,\pi]$, its arithmetic Fourier mean satisfies

$$
\sigma_N(f;x)=\frac1{N+1}\sum_{n=0}^{N}s_n(f;x)
=\frac1{2\pi}\int_{-\pi}^{\pi}K_N(t)f(x-t)\,dt.
$$

The coefficient integrals and the Dirichlet and Fejer convolution integrals are genuine tagged Riemann integrals, with the same values as the interval integrals. If $f$ is continuous on $\mathbb R$, these means converge uniformly to $f$ on $[-\pi,\pi]$.

**Proof.** Pair positive and negative exponentials to obtain the cosine formula for $D_N$. The cosine addition identities give

$$
(1-\cos t)D_n(t)=\cos(nt)-\cos((n+1)t).
$$

Summing this identity gives the quotient formula away from $2\pi\mathbb Z$. At a multiple of $2\pi$, $D_n=2n+1$, whose arithmetic mean is $N+1$. Continuity and evenness follow from the finite cosine sums, so these are the continuous values at the removable singularities. The quotient has nonnegative numerator and denominator; the values at the singularities are positive. Each nonconstant cosine has integral zero on $[-\pi,\pi]$, hence $\int D_n=2\pi$ and $\int K_N=2\pi$. Finally, cosine decreases on $[0,\pi]$, so $1-\cos t\ge1-\cos\delta>0$ in the stated region, while the numerator is at most $2$. This proves the off-zero bound, including $\delta=\pi$ when the region is nonempty.

For each Fourier mode, change variables $u=x-t$ and use periodicity to move the resulting interval back to $[-\pi,\pi]$. This gives

$$
\frac1{2\pi}\int_{-\pi}^{\pi}e^{int}f(x-t)\,dt=c_n(f)e^{inx}.
$$

Sum over the finite symmetric set of modes to obtain the Dirichlet convolution, then average over $n=0,\ldots,N$. Periodic Riemann integrability extends to every finite interval, and affine reflection preserves it. Multiplication by a continuous kernel preserves the tagged Riemann integral. These facts construct the source integrals before identifying their values with the interval integrals. The same Fourier normalization also gives Parseval for any square-integrable function on an interval of length $2\pi$.

Evenness and total mass give $\int_0^\pi K_N=\pi$. The off-zero estimate implies that $K_N/\pi$ tends uniformly to zero outside every neighborhood of zero in $[-\pi,\pi]$. Thus the half-interval approximate-identity theorem applies: for any real Banach space $E$, integrable $g:(0,\pi]\to E$, and right limit $g(t)\to a$ at zero,

$$
\int_0^\pi\frac{K_N(t)}\pi g(t)\,dt\longrightarrow a.
$$

Indeed, near zero the difference $g-a$ is small and the kernel has mass at most one; away from zero its integral tends to zero by uniform kernel decay and integrability. Reflecting the negative half of the convolution gives

$$
\sigma_N(f;x)=\int_0^\pi\frac{K_N(t)}\pi\frac{f(x-t)+f(x+t)}2\,dt.
$$

For continuous $f$, apply the Banach-valued result with $E=C([-\pi,\pi],\mathbb C)$ and $g(t)(x)=(f(x-t)+f(x+t))/2$. Joint continuity and compactness make this a continuous map into the supremum norm, with $g(0)=f$. Convergence in that norm is the required uniform convergence.

**Lean declarations:** `Rudin.Chapter08.dirichletKernel_eq_int_sum`, `Rudin.Chapter08.exercise15_kernel_formula`, `Rudin.Chapter08.exercise15_kernel_at_multiple`, `Rudin.Chapter08.exercise15_continuous`, `Rudin.Chapter08.exercise15_nonnegative`, `Rudin.Chapter08.dirichletKernel_integral`, `Rudin.Chapter08.exercise15_mass`, `Rudin.Chapter08.exercise15_off_zero_bound`, `Rudin.Chapter08.fourierCoefficient_riemann`, `Rudin.Chapter08.fourierPartialSum_eq_int_sum`, `Rudin.Chapter08.fourier_mode_convolution`, `Rudin.Chapter08.fourierPartialSum_convolution`, `Rudin.Chapter08.exercise15_convolution`, `Rudin.Chapter08.periodic_riemann_reflected_source`, `Rudin.Chapter08.exercise15_convolution_riemann`, `Rudin.Chapter08.fourierPartialSum_convolution_riemann`, `Rudin.Chapter08.fejerKernel_even`, `Rudin.Chapter08.fejerKernel_half_mass`, `Rudin.Chapter08.fejerKernel_uniform_off_zero`, `Rudin.Chapter08.fejerKernel_half_limit`, `Rudin.Chapter08.fejerMean_half_convolution`, `Rudin.Chapter08.exercise15_uniform_fejer`, `Rudin.Chapter08.fourierMonomial_bridge`, `Rudin.Chapter08.fourierCoefficient_bridge`, `Rudin.Chapter08.source_parseval`.

<a id="r08e16"></a>
### 8.16 — Fejer convergence at a jump

**Lean source:** [Exercise16.lean](../../Math/Rudin/Chapter08/Exercise16.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $f:\mathbb R\to\mathbb C$ be $2\pi$-periodic and Riemann integrable on $[-\pi,\pi]$. At any real $x$ where the finite one-sided limits $L=f(x-)$ and $R=f(x+)$ exist,

$$
\sigma_N(f;x)\longrightarrow\frac{L+R}{2}.
$$

This is a pointwise assertion at every such $x$, not an almost-everywhere assertion. At joins of periods the limits are those of the periodic function; its assigned value at $x$ need not equal either limit.

**Proof.** As $t\downarrow0$, the points $x-t$ approach $x$ from the left and $x+t$ approach it from the right. Consequently $g(t)=(f(x-t)+f(x+t))/2$ tends to $(L+R)/2$. The translated and reflected functions are integrable on $[0,\pi]$. Exercise 15 expresses $\sigma_N(f;x)$ as $\int_0^\pi(K_N/\pi)g$; its half-interval approximate-identity theorem gives the limit.

**Lean declarations:** `Rudin.Chapter08.exercise16_pointwise_fejer`.

<a id="r08e17"></a>
### 8.17 — Fourier convergence under monotonicity

**Lean source:** [Exercise17.lean](../../Math/Rudin/Chapter08/Exercise17.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $f:\mathbb R\to\mathbb R$ be either nondecreasing or nonincreasing on $[-\pi,\pi)$, with $|f|\le M$ there. For every integer $n$, including zero and negative integers,

$$
|n c_n(f)|\le\frac{2M}{\pi}.
$$

For its $2\pi$-periodic extension $F$, both finite one-sided limits exist at every real $x$, and

$$
s_N(f;x)\longrightarrow\frac{F(x-)+F(x+)}2.
$$

In particular, this holds for already periodic $f$. More locally, suppose $f$ is Riemann integrable on $[-\pi,\pi]$, $-\pi\le\alpha<\beta\le\pi$, and $f$ is monotone in either direction on $(\alpha,\beta)$. At each $x$ in that open interval both one-sided limits exist and $s_N(f;x)$ tends to their average. No monotonicity outside that interval is required. Existence of the local one-sided limits uses only the local monotonicity, without the global Riemann-integrability assumption.

**Proof.** First let $f$ be nondecreasing on the closed fundamental interval. Apply the Chapter 6 Riemann–Stieltjes integration-by-parts theorem to $G(t)=e^{-int}$, whose modulus is one. It constructs the integrals and gives

$$
\int_{-\pi}^{\pi}f(t)G'(t)\,dt
=f(\pi)G(\pi)-f(-\pi)G(-\pi)-\int_{-\pi}^{\pi}G\,df.
$$

The last integral has modulus at most $f(\pi)-f(-\pi)\le2M$, and the two boundary terms contribute at most $2M$. Since $G'=-inG$, division by $2\pi$ gives the asserted bound. For half-open data set the missing right endpoint to $M$; this preserves monotonicity and the bound. Changing that single endpoint does not change any Fourier coefficient. Apply the increasing result to $-f$ for the decreasing case. The estimate is trivial at $n=0$.

Bounded monotone functions have finite endpoint and interior one-sided limits. Reduction modulo $2\pi$ and periodic translation transfer these limits to every real point, including the joined endpoints. They are also Riemann integrable: their interior discontinuities form a countable set, and endpoint changes do not affect integrability. Exercise 16 therefore gives convergence of the arithmetic Fourier means. If $S_N=s_N(f;x)$, the coefficient bound and $|e^{inx}|=1$ give

$$
|N(S_N-S_{N-1})|\le\frac{4M}{\pi}\quad(N\ge1).
$$

The bounded-increment Tauberian converse proved in Chapter 3, Exercise 14(e), then transfers convergence of the means to $S_N$ itself. This uses the valid final converse; the zero-bound correction to that earlier exercise's strict intermediate estimate does not require an additional assumption here.

For the local assertion, choose $\alpha<c<x<d<\beta$ and put $g(t)=f(\max(c,\min(d,t)))$. This is globally monotone, bounded on the fundamental interval, and equal to $f$ near $x$. Its Fourier sums have the asserted limit, and local equality identifies its two limits with those of $f$.

The proved localization result applies to interval-integrable complex functions $u,v$, an interior point $x\in(-\pi,\pi)$, a radius $\delta>0$ with $u=v$ whenever $|t-x|<\delta$, and a uniform bound on $|u-v|$ on the closed fundamental interval. Define $h(t)=(u(t)-v(t))/(1-\cos(x-t))$ away from that neighborhood and zero inside. The denominator is bounded away from zero on the remaining compact set, so $h$ is square integrable. The identity

$$
(1-\cos y)D_N(y)=\cos(Ny)-\cos((N+1)y)
$$

expresses $s_N(u;x)-s_N(v;x)$ as the difference of two normalized cosine integrals of $h$. Parseval implies that its Fourier coefficients tend to zero along both positive and negative frequencies, so both cosine integrals tend to zero. The boundedness required here follows for $f$ from its literal Riemann integrability and for $g$ from monotonicity. Localization completes the proof and also confirms existence of the local one-sided limits without assumptions at $\alpha$ or $\beta$.

**Lean declarations:** `Rudin.Chapter08.exercise17_coefficient_bound`, `Rudin.Chapter08.exercise17_bounded_coefficients`, `Rudin.Chapter08.exercise17_fourier_limit`, `Rudin.Chapter08.exercise17_one_sided_limits`, `Rudin.Chapter08.exercise17_pointwise`, `Rudin.Chapter08.exercise17_periodic_extension_limit`, `Rudin.Chapter08.exercise17_local_monotone`, `Rudin.Chapter08.exercise17_local_one_sided_limits`, `Rudin.Chapter08.exercise17_localization`.

<a id="r08e18"></a>
### 8.18 — Two strict trigonometric signs

**Lean source:** [Exercise18.lean](../../Math/Rudin/Chapter08/Exercise18.lean).

**Inventory status:** Verified as stated.

**Statement.** Throughout $0<x<\pi/2$, both functions are strictly negative:

$$
x^3-\sin^2x\tan x<0,\qquad
2x^2-\sin^2x-x\tan x<0.
$$

**Proof.** Set $A(t)=\sin t-t\cos t$. It vanishes at zero and $A'(t)=t\sin t>0$, so $A(t)>0$ on the stated interval. Next set $B(t)=t(1+2\cos^2t)-3\sin t\cos t$. Again $B(0)=0$, while $B'(t)=4\sin t\,A(t)>0$, hence $B(t)>0$.

Use the continuous value $\operatorname{sinc}(0)=1$. For $0<t<\pi/2$, differentiation gives

$$
\frac{d}{dt}\frac{\operatorname{sinc}^3t}{\cos t}
=\frac{\sin^2t\,t^2 B(t)}{(t^3\cos t)^2}>0.
$$

The quotient is continuous from zero to $x$ because cosine is positive there, and its value at zero is $1$. Thus $\sin^3x/(x^3\cos x)>1$, proving the first strict sign.

Put $a=\sin^2x$ and $b=x\tan x$. Both are positive. Multiplication of the first inequality by $x>0$ gives $ab>x^4$. Since $(a-b)^2\ge0$, $(a+b)^2\ge4ab>4x^4$. Positivity of $a+b$ gives $a+b>2x^2$, which is the second strict sign. No endpoint assertion at $\pi/2$, where tangent is undefined, is used.

**Lean declarations:** `Rudin.Chapter08.exercise18_first_sign`, `Rudin.Chapter08.exercise18_second_sign`.

<a id="r08e19"></a>
### 8.19 — Means along an irrational rotation

**Lean source:** [Exercise19.lean](../../Math/Rudin/Chapter08/Exercise19.lean).

**Inventory status:** Verified as stated.

**Statement.** If $f:\mathbb R\to\mathbb C$ is continuous and $2\pi$-periodic and $\alpha/\pi$ is irrational, then for every real $x$,

$$
\frac1N\sum_{n=1}^{N}f(x+n\alpha)
\longrightarrow\frac1{2\pi}\int_{-\pi}^{\pi}f(t)\,dt.
$$

The same statement holds for real-valued $f$. The displayed integral is also its tagged Riemann integral.

**Proof.** Regard $f$ as a continuous function on $\mathbb R/(2\pi\mathbb Z)$. The zero Fourier mode is constant, so its average and mean are both $1$. For a nonzero integer $k$, irrationality implies $q=e^{ik\alpha}\ne1$: otherwise $k\alpha=2\pi m$ for an integer $m$, making $\alpha/\pi$ rational. The geometric-sum formula gives

$$
\frac1N\sum_{n=1}^{N}e^{ik(x+n\alpha)}
=\frac{e^{ikx}q}{N}\frac{q^N-1}{q-1}\longrightarrow0,
$$

because $|q|=1$ and $|q^N-1|\le2$. This equals the period mean of the nonzero mode.

Both the rotation average and normalized period integral have operator norm at most one in the supremum norm. Their difference therefore has Lipschitz constant at most two, independently of $N$. Convergence to zero holds on the linear span of the Fourier modes, which is dense in the continuous functions on the circle. The uniform operator bound makes the set of functions with this convergence closed, so it contains every continuous function. Conversion of normalized Haar measure on the circle to an interval of length $2\pi$ gives the displayed mean. Taking real parts gives the real version. Continuity on the closed interval constructs the tagged Riemann value and identifies it with the interval integral. The harmless $N=0$ value of the formal sequence has no effect on its limit.

**Lean declarations:** `Rudin.Chapter08.exercise19_irrational_rotation_mean`, `Rudin.Chapter08.exercise19_real`, `Rudin.Chapter08.exercise19_riemann_integral`.

<a id="r08e20"></a>
### 8.20 — Factorial bounds from logarithmic graphs

**Lean source:** [Exercise20.lean](../../Math/Rudin/Chapter08/Exercise20.lean).

**Inventory status:** Verified as stated.

**Statement.** Define a lower graph $F$ by the straight chord from $(m,\log m)$ to $(m+1,\log(m+1))$, and an upper graph $G$ by the tangent at $m$, restricted to $[m-1/2,m+1/2)$, for integers $m\ge1$. Explicitly,

$$
F(x)=(m+1-x)\log m+(x-m)\log(m+1)\quad(m\le x\le m+1),
$$

$$
G(x)=x/m-1+\log m\quad(m-1/2\le x<m+1/2).
$$

Then $F(x)\le\log x\le G(x)$ for $x\ge1$. For every integer $n\ge1$ the genuine Darboux integral values are

$$
\int_1^n F=\log(n!)-\tfrac12\log n,\qquad
\int_1^n G=\log(n!)-\tfrac12\log n+\tfrac18-\frac1{8n},
$$

$$
\int_1^n\log x\,dx=n\log n-n+1.
$$

For $n\ge2$ this gives $\int_1^n F>-1/8+\int_1^n G$ and

$$
\frac78<\log(n!)-(n+\tfrac12)\log n+n<1,
$$

$$
e^{7/8}<\frac{n!}{(n/e)^n\sqrt n}<e.
$$

**Proof.** The graphs can be specified globally using $m=\lfloor x\rfloor$ for $F$ and $m=\lfloor x+1/2\rfloor$ for $G$ on $x\ge1$. Adjacent chord formulas agree at integer endpoints. The upper cells are half-open and select exactly one tangent value at each join. Concavity of logarithm puts each chord below its graph, strictly below inside a unit interval. The inequality $\log u\le u-1$, applied to $u=x/m>0$, puts logarithm below the selected tangent.

The chord integral on $[m,m+1]$ is $(\log m+\log(m+1))/2$. Adding cells gives the formula for $\int F$. Split each interval $[m,m+1]$ at $m+1/2$ for $G$. Integrating its two affine pieces gives

$$
\int_m^{m+1}G=\frac{\log m+\log(m+1)}2+\frac1{8m}-\frac1{8(m+1)}.
$$

The correction telescopes. The finite endpoint changes in the tangent pieces do not affect the Darboux integral; boundedness and continuity except at those endpoints establish its existence. The formulas also cover $n=1$, where all integrals vanish. Their difference is $1/8-1/(8n)<1/8$, proving the strict integral comparison.

Integration of $F\le\log\le G$ is legitimate for these constructed integrals. The first comparison is strict for $n\ge2$, because $F<\log$ throughout $(1,2)$, a set of positive length. If $A_n=\log(n!)-(n+1/2)\log n+n$, the two comparisons give $A_n<1$ and $A_n\ge7/8+1/(8n)>7/8$. Finally the positive factorial ratio has logarithm $A_n$, using $\log\sqrt n=(\log n)/2$. Exponentiation gives the two ratio bounds. No Stirling asymptotic is needed.

**Lean declarations:** `Rudin.Chapter08.exercise20_lower_graph`, `Rudin.Chapter08.exercise20_upper_graph`, `Rudin.Chapter08.exercise20_log_bounds`, `Rudin.Chapter08.exercise20_lower_integral`, `Rudin.Chapter08.exercise20_upper_integral`, `Rudin.Chapter08.exercise20_integral_comparison`, `Rudin.Chapter08.exercise20_log_integral`, `Rudin.Chapter08.exercise20_log_factorial`, `Rudin.Chapter08.exercise20_factorial_ratio`.

<a id="r08e21"></a>
### 8.21 — Logarithmic growth of Dirichlet kernel norms

**Lean source:** [Exercise21.lean](../../Math/Rudin/Chapter08/Exercise21.lean).

**Inventory status:** Verified as stated.

**Statement.** Put $L_n=(2\pi)^{-1}\int_{-\pi}^{\pi}|D_n(t)|\,dt$. For every integer $n\ge1$,

$$
\frac4{\pi^2}\log n<L_n,\qquad
0\le L_n-\frac4{\pi^2}\log n\le3+\frac4{\pi^2}.
$$

Thus the requested positive lower-bound constant can be $4/\pi^2$, and the error sequence is bounded in absolute value. More precisely, with $H_n=\sum_{j=1}^{n}1/j$, the source proves $4H_n/\pi^2\le L_n\le3+4H_n/\pi^2$ even for $n=0$.

**Proof.** The sine addition formulas and induction give $\sin(t/2)D_n(t)=\sin((n+1/2)t)$. For $0<u\le\pi/2$, elementary sine estimates imply

$$
0\le\frac1{\sin u}-\frac1u\le1.
$$

For the upper bound use $\sin u\ge u/2$ and $\sin u\ge u-u^3/6$, which imply $u-\sin u\le u\sin u$ in this range. Since $|\sin v|\le1$, multiplication gives

$$
(2n+1)|\operatorname{sinc}((2n+1)u)|
\le |D_n(2u)|
\le(2n+1)|\operatorname{sinc}((2n+1)u)|+1.
$$

Evenness and the change of variables $t=2u$ express $L_n$ as $(2/\pi)\int_0^{\pi/2}|D_n(2u)|\,du$. The main comparison integral becomes $\int_0^{(n+1/2)\pi}|\operatorname{sinc}v|\,dv$.

On each sine lobe $[k\pi,(k+1)\pi]$, $\int|\sin v|=2$. Dividing by the largest denominator gives a lower lobe bound $2/((k+1)\pi)$; for $k\ge1$, dividing by the smallest denominator gives an upper bound $2/(k\pi)$. The initial lobe is at most $\pi$ because $|\operatorname{sinc}|\le1$. Positivity permits comparison of the cutoff $(n+1/2)\pi$ with $n\pi$ and $(n+1)\pi$. Adding the lobe estimates and the additive kernel error gives precisely the stated harmonic bounds. All integrands used here are continuous at zero through the sinc value, so no singular integral is assumed.

Finally $\log(n+1)\le H_n\le1+\log n$ for $n\ge1$, and $\log n<\log(n+1)$. Substitution gives the strict logarithmic lower bound, including $n=1$, and the explicit two-sided error estimate. Nonnegativity of that error converts its upper bound into an absolute-value bound.

**Lean declarations:** `Rudin.Chapter08.e21_harmonic_bounds`, `Rudin.Chapter08.exercise21_log_lower_bound`, `Rudin.Chapter08.exercise21_error_bounds`, `Rudin.Chapter08.exercise21_bounded_error`.

<a id="r08e22"></a>
### 8.22 — The binomial series and its differential equation
**Lean source:** [Exercise22.lean](../../Math/Rudin/Chapter08/Exercise22.lean).
**Inventory status:** Verified as stated.

**Statement.** For $\alpha\in\mathbb R$, define

$$
c_0=1,\qquad c_n=\frac{\alpha(\alpha-1)\cdots(\alpha-n+1)}{n!}\quad(n\ge1).
$$

For every $|x|<1$, the series $F(x)=\sum_{n\ge0}c_nx^n$ converges absolutely, and its ordered partial sums converge to $F(x)$. If $\alpha=m\in\mathbb N$, every coefficient with $n>m$ vanishes. The sum is differentiable on $(-1,1)$ and satisfies

$$
(1+x)F'(x)=\alpha F(x),\qquad F(0)=1.
$$

The unique differentiable solution of this equation with initial value one is $F(x)=(1+x)^\alpha$. Thus

$$
(1+x)^\alpha=1+\sum_{n\ge1}\frac{\alpha(\alpha-1)\cdots(\alpha-n+1)}{n!}x^n.
$$

For $\alpha>0$ and $-1<x<1$, the file also proves the absolutely convergent Gamma expansion

$$
(1-x)^{-\alpha}=\sum_{n\ge0}\frac{\Gamma(n+\alpha)}{n!\,\Gamma(\alpha)}x^n.
$$

Both identities include convergence of ordered partial sums. The endpoints $x=\pm1$ are not asserted. The bases $1+x$ and $1-x$ are positive throughout the stated interval.

**Proof.** The coefficient is the falling product divided by $n!$, with the empty product equal to one. If $\alpha=m\in\mathbb N$ and $n>m$, the factor with index $m$ is zero, so the series terminates. Otherwise its coefficients are nonzero and

$$
\frac{|c_{n+1}|}{|c_n|}=\frac{|\alpha-n|}{n+1}\longrightarrow1.
$$

For $0<|x|<1$, the ratio test gives absolute convergence; at $x=0$ only the constant term survives. Equivalently, the radius of convergence is at least one, which is the library result used in Lean. Absolute convergence supplies ordered convergence.

Inside that radius, the power-series differentiation theorem gives

$$
F'(x)=\sum_{n\ge0}(n+1)c_{n+1}x^n.
$$

The falling-product formula gives $(n+1)c_{n+1}=(\alpha-n)c_n$. Reindexing the absolutely convergent derivative series yields

$$
xF'(x)=\sum_{n\ge0}nc_nx^n.
$$

Add the two series term by term to obtain $(1+x)F'(x)=\alpha\sum_{n\ge0}c_nx^n=\alpha F(x)$. At zero the constant coefficient gives $F(0)=1$.

To solve the differential equation, let $f$ be any differentiable solution on $(-1,1)$ with $f(0)=1$. The product rule and the equation give

$$
\frac{d}{dx}\bigl(f(x)(1+x)^{-\alpha}\bigr)=0.
$$

The interval is connected, so this product is constant, and its value at zero is one. Since $(1+x)^\alpha>0$, this proves $f(x)=(1+x)^\alpha$. Apply this to the power-series sum to obtain the binomial identity.

Finally, for $\alpha>0$, positivity of $\Gamma(\alpha)$ and the recurrence $\Gamma(u+1)=u\Gamma(u)$ give

$$
(-1)^n\binom{-\alpha}{n}
=\frac{\alpha(\alpha+1)\cdots(\alpha+n-1)}{n!}
=\frac{\Gamma(n+\alpha)}{n!\,\Gamma(\alpha)}.
$$

For $n=0$ the empty product gives one. Substitute exponent $-\alpha$ and argument $-x$ into the binomial identity and use this coefficient formula. Its absolute convergence also gives the asserted ordered Gamma-series convergence.

**Lean declarations:** `exercise22_coefficient`, `exercise22_hasSum`, `exercise22_ordered_convergence`, `exercise22_terminates`, `exercise22_differentiable`, `exercise22_series_ode`, `exercise22_initial_value`, `exercise22_ode_unique`, `exercise22_binomial_identity`, `exercise22_newton`, `exercise22_gamma_hasSum`, `exercise22_gamma_series`.

<a id="r08e23"></a>
### 8.23 — Integral index and signed turns

**Lean source:** [Exercise23.lean](../../Math/Rudin/Chapter08/Exercise23.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $a\le b$ and let $\gamma:[a,b]\to\mathbb C$ be closed and nowhere zero. Assume a continuous velocity $v$ gives its derivative within $[a,b]$ at every point, including the endpoints. Then

$$
\operatorname{Ind}(\gamma)=\frac1{2\pi i}\int_a^b\frac{v(t)}{\gamma(t)}\,dt\in\mathbb Z.
$$

The logarithmic derivative has a genuine tagged Riemann integral on the whole interval and every closed subinterval. Its integral index agrees with that computed using the canonical within derivative. For every integer $n$, the curve $e^{int}$ on $[0,2\pi]$ has index $n$, including $n=0$ and negative $n$. There exist continuous real functions $\rho>0$ and $\theta$ on $[a,b]$, with $\theta(a)=0$, such that

$$
\gamma(t)=\gamma(a)\rho(t)e^{i\theta(t)},\qquad
\theta(b)-\theta(a)=2\pi\operatorname{Ind}(\gamma).
$$

**Proof.** The derivative assumption makes $\gamma$ continuous; nonvanishing makes $v/\gamma$ continuous. This constructs its tagged Riemann integrals and identifies them with the interval integrals, also on every ordered subinterval. Put $\Phi(t)=\int_a^t v/\gamma$. The fundamental theorem of calculus supplies its within derivative $v/\gamma$, so differentiation gives

$$
\frac{d}{dt}\bigl(\gamma(t)e^{-\Phi(t)}\bigr)=0.
$$

The zero-derivative theorem on a segment makes this product equal to $\gamma(a)$. At $b$, closure and $\gamma(a)\ne0$ imply $e^{\Phi(b)}=1$. The kernel of the complex exponential is $2\pi i\mathbb Z$, hence $\Phi(b)=2\pi i n$ and the index is the integer $n$.

For $e^{int}$ the continuous velocity is $in e^{int}$; its logarithmic derivative is the constant $in$, whose integral is $2\pi i n$. This verifies closure and the index for every integer sign. For the polar representation take $\rho(t)=e^{\operatorname{Re}\Phi(t)}$ and $\theta(t)=\operatorname{Im}\Phi(t)$. The product identity gives the representation, and $\Phi(b)=2\pi i n$ gives the total angular change. Thus positive and negative indices count net turns in opposite orientations, while zero means zero net angular change, not necessarily a constant curve.

On a nondegenerate interval uniqueness of the within derivative identifies $v$ with that derivative. If $a=b$, the integral is zero independently of the nonunique derivative jet, and the index is zero; the same representation has $\rho(a)=1$ and $\theta(a)=0$.

**Lean declarations:** `Rudin.Chapter08.exercise23_integer_index`, `Rudin.Chapter08.IsC1NonzeroLoop.riemann_logDerivative`, `Rudin.Chapter08.IsC1NonzeroLoop.riemann_logDerivative_subinterval`, `Rudin.Chapter08.IsC1NonzeroLoop.index_eq_riemann_value`, `Rudin.Chapter08.IsC1NonzeroLoop.index_eq_derivWithin`, `Rudin.Chapter08.IsC1NonzeroLoop.primitive_derivative`, `Rudin.Chapter08.IsC1NonzeroLoop.primitive_identity`, `Rudin.Chapter08.IsC1NonzeroLoop.exp_integral_eq_one`, `Rudin.Chapter08.exercise23_circle`, `Rudin.Chapter08.exercise23_signed_turns`.

<a id="r08e24"></a>
### 8.24 — Zero index in the slit plane

**Lean source:** [Exercise24.lean](../../Math/Rudin/Chapter08/Exercise24.lean).

**Inventory status:** Verified as stated.

**Statement.** A closed nonzero curve on $[a,b]$, $a\le b$, with a continuous within derivative as in Exercise 23 has index zero if its entire range is in $\mathbb C\setminus(-\infty,0]$.

**Proof.** The principal logarithm is differentiable on this slit plane. The chain rule gives within derivative $v(t)/\gamma(t)$ for $\log\gamma(t)$. The fundamental theorem of calculus, using the continuous logarithmic derivative, gives

$$
\int_a^b\frac{v(t)}{\gamma(t)}\,dt
=\log\gamma(b)-\log\gamma(a)=0.
$$

The endpoint equality uses closure and the same single-valued logarithm throughout. Normalizing by $2\pi i$ gives index zero, also on a singleton interval.

**Lean declarations:** `Rudin.Chapter08.exercise24_zero_index`.

<a id="r08e25"></a>
### 8.25 — Stability of the index under a strict perturbation

**Lean source:** [Exercise25.lean](../../Math/Rudin/Chapter08/Exercise25.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $\gamma_1,\gamma_2$ be closed nonzero curves on the same ordered interval $[a,b]$, each with a continuous within derivative $v_1,v_2$. If

$$
|\gamma_1(t)-\gamma_2(t)|<|\gamma_1(t)|\quad(a\le t\le b),
$$

then their indices are equal. More generally, the index of their quotient is the difference of their indices.

**Proof.** The quotient $q=\gamma_2/\gamma_1$ is again a closed nonzero curve with continuous within derivative

$$
q'=\frac{v_2\gamma_1-\gamma_2v_1}{\gamma_1^2},\qquad
\frac{q'}q=\frac{v_2}{\gamma_2}-\frac{v_1}{\gamma_1}.
$$

All denominators are nonzero. Integration proves $\operatorname{Ind}(q)=\operatorname{Ind}(\gamma_2)-\operatorname{Ind}(\gamma_1)$. The strict hypothesis gives $|1-q(t)|<1$, and therefore $\operatorname{Re}q(t)>0$. Thus the quotient lies in the slit plane and Exercise 24 gives its index zero. Subtraction proves the claim.

**Lean declarations:** `Rudin.Chapter08.IsC1NonzeroLoop.div`, `Rudin.Chapter08.curveIndex_div`, `Rudin.Chapter08.quotient_mem_slitPlane`, `Rudin.Chapter08.exercise25_index_stability`.

<a id="r08e26"></a>
### 8.26 — The index of a continuous loop

**Lean source:** [Exercise26.lean](../../Math/Rudin/Chapter08/Exercise26.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $\gamma:[0,2\pi]\to\mathbb C$ be continuous, closed, and nowhere zero. There is $\delta>0$ with $|\gamma(t)|>\delta$ everywhere, and a finite complex trigonometric polynomial $P(t)=\sum_k a_ke^{ikt}$ with $|P(t)-\gamma(t)|<\delta/4$ throughout the closed interval. Such polynomials are closed, continuously differentiable, and nonzero. Their integral indices agree, independently of both the polynomial and the admissible $\delta$. This common integer defines $\operatorname{Ind}(\gamma)$.

It agrees with the integral index when $\gamma$ has a continuous within derivative. Without any derivative assumption, a loop in the slit plane has index zero, and two continuous nonzero loops have equal indices under the strict perturbation condition of Exercise 25. Arbitrarily accurate polynomial approximations can also satisfy $|P-\gamma|<|\gamma|/4$ pointwise. Uniform trigonometric approximation itself needs only continuity and equal endpoint values, not nonvanishing.

**Proof.** Compactness gives a positive minimum of $|\gamma|$; half that minimum is an admissible $\delta$. Identify the two interval endpoints to obtain a continuous function on the circle. Density of the linear span of the integer Fourier modes produces an actual finite trigonometric polynomial within any specified positive uniform error, including at the identified endpoints. Differentiating the finite sum gives continuous velocity $\sum_k a_k ik e^{ikt}$. The quarter-norm estimate excludes zero.

If $p,q$ both approximate $z$ with errors less than $|z|/4$, then

$$
|p-q|<|z|/2<|p|,
$$

where the last inequality follows from $|p|>3|z|/4$. Exercise 25 therefore equates the integral indices of any two such polynomials. Every admissible $\delta/4$ approximation meets this relative estimate, even if the two chosen deltas differ. Choose one polynomial and take the integer supplied by Exercise 23; the equality just proved makes the definition independent of the choices. The same comparison works for any smooth quarter-norm approximation. Taking the smooth curve to be $\gamma$ itself proves agreement with its integral index.

If the range of $\gamma$ is in the slit plane, its compact image has a uniform neighborhood still in that open set. Choose the polynomial both inside this neighborhood and within the relative quarter-norm bound. Exercise 24 gives its integral index zero, hence the continuous index is zero.

For two strictly close loops, the positive continuous margin $m(t)=|\gamma_1(t)|-|\gamma_1(t)-\gamma_2(t)|$ has a positive uniform lower bound $\varepsilon$. Choose approximants $P,Q$ each within $\varepsilon/4$ of its loop and within its relative quarter-norm bound. Triangle inequalities give $|P-Q|<|P|$: the loss from the two approximation errors and the lower estimate for $|P|$ is less than $3\varepsilon/4<m(t)$. Smooth stability equates their integral indices, and each computes its original loop's continuous index.

**Lean declarations:** `Rudin.Chapter08.exercise26_trigonometric_approximation`, `Rudin.Chapter08.IsContinuousNonzeroLoop.approximants`, `Rudin.Chapter08.IsContinuousNonzeroLoop.close_polynomial`, `Rudin.Chapter08.exercise26_approximant_index`, `Rudin.Chapter08.exercise26_independence`, `Rudin.Chapter08.continuousCurveIndex_spec`, `Rudin.Chapter08.continuousCurveIndex_eq_smooth`, `Rudin.Chapter08.exercise26_smooth_agreement`, `Rudin.Chapter08.exercise26_negative_axis_extension`, `Rudin.Chapter08.exercise26_perturbation_extension`.

<a id="r08e27"></a>
### 8.27 — A zero forced by positive asymptotic degree

**Lean source:** [Exercise27.lean](../../Math/Rudin/Chapter08/Exercise27.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $f:\mathbb C\to\mathbb C$ be continuous. Suppose $n$ is a positive integer, $c\ne0$, and

$$
z^{-n}f(z)\longrightarrow c\quad\text{as }|z|\longrightarrow\infty.
$$

Then $f$ has a zero. Under the hypothetical assumption that $f$ is nowhere zero, the loops $\gamma_r(t)=f(re^{it})$, $0\le t\le2\pi$, satisfy: $\operatorname{Ind}(\gamma_0)=0$; $\operatorname{Ind}(\gamma_r)=n$ for every sufficiently large positive $r$; and their integer index is continuous on $[0,\infty)$.

**Proof.** A continuous family of nonzero loops has continuous, in fact locally constant, index. To prove this, fix one loop and a positive uniform lower bound $\delta$ for its modulus. Joint continuity on the compact parameter interval gives nearby loops within $\delta$ in the supremum norm. Exercise 26's strict perturbation theorem equates their indices. This argument applies to any topological family parameter space with the stated joint continuity. A constant nonzero loop has index zero by smooth agreement and zero velocity; this does not require its constant value to avoid the negative axis. These facts prove the zero-radius assertion and continuity of the radial index.

The asymptotic hypothesis is used in its equivalent epsilon-radius form. Choose the error $|c|$. For every sufficiently large $r>0$ and every $z=re^{it}$,

$$
|f(z)-cz^n|=|z|^n|z^{-n}f(z)-c|<|c|\,|z|^n=|cz^n|.
$$

The comparison loop is $cr^ne^{int}$. Multiplication of the integer-speed circle by a nonzero constant cancels in the logarithmic derivative, so its index is $n$. Continuous perturbation stability gives the same index for $\gamma_r$. This proves the large-radius fact directly from the estimate, without using the eventual contradiction.

Finally $[0,\infty)$ is connected, and a continuous integer-valued function on it is constant. Its value at zero is $0$, but its value at a sufficiently large radius is $n>0$, a contradiction. Therefore some $z$ satisfies $f(z)=0$. The formal result includes both the epsilon-radius and filter-limit formulations of the hypothesis.

**Lean declarations:** `Rudin.Chapter08.continuous_family_index`, `Rudin.Chapter08.continuousCurveIndex_const`, `Rudin.Chapter08.scaled_circle_index`, `Rudin.Chapter08.exercise27_a`, `Rudin.Chapter08.exercise27_b`, `Rudin.Chapter08.hasPositiveAsymptoticDegree_iff`, `Rudin.Chapter08.exercise27_c`, `Rudin.Chapter08.exercise27_zero_existence`, `Rudin.Chapter08.exercise27_index_facts`, `Rudin.Chapter08.exercise27_zero_of_tendsto`.

<a id="r08e28"></a>
### 8.28 — An antipodal value on the boundary

**Lean source:** [Exercise28.lean](../../Math/Rudin/Chapter08/Exercise28.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $D=\{z\in\mathbb C:|z|\le1\}$ and $T=\{z:|z|=1\}$, with their induced topologies. For every continuous $g:D\to T$, there is a boundary point $z\in T$ such that $g(z)=-z$.

**Proof.** Suppose no boundary point has that property. The loops $H_r(t)=g(re^{it})$, $0\le r\le1$, are continuous, closed, and have modulus one. Their indices vary continuously with $r$, hence are constant. At $r=0$ the loop is constant, so every $H_r$ has index zero.

Write $E(t)=e^{it}$, whose index is one. On the boundary $H_1(t)\ne-E(t)$. For unit vectors $w,z$, the identity

$$
|w-z|^2+|w+z|^2=4
$$

shows that non-antipodality implies $|w-z|<2$. Thus the midpoint loop $M=(H_1+E)/2$ is nonzero and satisfies both

$$
|E-M|<|E|=1,\qquad |H_1-M|<|H_1|=1.
$$

Apply continuous index stability first to $E,M$ and then to $H_1,M$. It gives $\operatorname{Ind}(H_1)=\operatorname{Ind}(E)=1$, contradicting the radial index zero. The contradiction concerns the boundary loop, so the resulting witness has modulus exactly one, not merely at most one.

**Lean declarations:** `Rudin.Chapter08.unit_distance_lt_two`, `Rudin.Chapter08.exercise28_boundary_antipode`.

<a id="r08e29"></a>
### 8.29 — A disc fixed point from the ray construction

**Lean source:** [Exercise29.lean](../../Math/Rudin/Chapter08/Exercise29.lean).

**Inventory status:** Verified as stated.

**Statement.** Every continuous $f:D\to D$ has a fixed point. Under the contrary assumption, the ray starting at $f(z)$ and passing through $z$ defines a continuous boundary map $g:D\to T$ with $g(z)=z$ on $T$. Its explicit parameter and uniqueness include boundary inputs.

**Proof.** For distinct $z,w\in D$, put

$$
A=|w-z|^2>0,\qquad B=\operatorname{Re}(\overline z(w-z)),\qquad C=|z|^2-1\le0.
$$

Expansion gives

$$
|z-s(w-z)|^2-1=As^2-2Bs+C,\qquad A+2B+C=|w|^2-1\le0.
$$

These coefficient conditions imply that the unique nonnegative quadratic root is

$$
s=\frac{B+\sqrt{B^2-AC}}A.
$$

Indeed, the discriminant is nonnegative, $\sqrt{B^2-AC}\ge-B$, and $\sqrt{B^2-AC}>B$. For $C<0$ the last inequality follows from $-AC>0$; for $C=0$ the geometric bound gives $B\le-A/2<0$. The other root is therefore negative. Equivalently, subtracting the root equations factors their difference by $A(t+s)-2B>0$ for $t\ge0$, proving uniqueness without a division by zero. Thus $g=z-s(w-z)$ is the unique circle intersection with a nonnegative parameter. Also $g=w+(1+s)(z-w)$ with $1+s\ge1$, so it is on the specified ray beyond or at $z$.

Assume $f$ has no fixed point and take $w=f(z)$. Then $A(z)>0$ everywhere. The displayed root formula uses continuous coefficients, the continuous square root, and a nonzero denominator. Consequently $s(z)$ and $g(z)$ are continuous, and the quadratic identity gives $|g(z)|=1$. If $|z|=1$, then $C=0$ and $s=0$ is a nonnegative root; uniqueness gives $g(z)=z$. This explicitly covers the boundary case, where an arbitrary choice between quadratic roots would be insufficient.

Exercise 28 supplies a boundary point with $g(z)=-z$. The boundary identity gives $z=-z$, hence $z=0$, contradicting $|z|=1$. Therefore $f$ has a fixed point. No library fixed-point theorem is used.

**Lean declarations:** `Rudin.Chapter08.exercise29_ray_boundary_map`, `Rudin.Chapter08.rayRoot_unique`, `Rudin.Chapter08.ray_coefficients`, `Rudin.Chapter08.ray_quadratic`, `Rudin.Chapter08.rayBoundaryPoint_on_ray`, `Rudin.Chapter08.exercise29_ray_map_continuity`, `Rudin.Chapter08.exercise29_ray_boundary_identity`, `Rudin.Chapter08.exercise29_disc_fixed_point`.

<a id="r08e30"></a>
### 8.30 — A Gamma ratio for every real shift

**Lean source:** [Exercise30.lean](../../Math/Rudin/Chapter08/Exercise30.lean).

**Inventory status:** Verified as stated.

**Statement.** For every fixed real $c$,

$$
\frac{\Gamma(x+c)}{x^c\Gamma(x)}\longrightarrow1\quad(x\longrightarrow+\infty).
$$

On the explicit eventual domain $x>\max(0,-c)$, both Gamma arguments and the complete denominator are positive. The proof also establishes real-argument logarithmic Stirling asymptotics:

$$
R(x)=\log\Gamma(x+1)-(x+\tfrac12)\log x+x
\longrightarrow\log\sqrt\pi+\tfrac12\log2.
$$

**Proof.** At positive integer $n$, the library factorial Stirling sequence gives $R(n)=\log(\mathrm{stirlingSeq}(n))+(\log2)/2$ and $\mathrm{stirlingSeq}(n)\to\sqrt\pi$. To pass to real arguments, log-convexity of Gamma and $\Gamma(x+1)=x\Gamma(x)$ give, for $n\ge1$ and $0\le t\le1$,

$$
t\log n\le\log\Gamma(n+t+1)-\log\Gamma(n+1)\le t\log(n+1).
$$

Together with $1-u^{-1}\le\log u\le u-1$ for $u>0$, these bounds imply $|R(n+t)-R(n)|\le2/n$. Taking $n=\lfloor x\rfloor$ transfers the integer limit to all real $x\to\infty$.

On the positive eventual domain, Gamma recurrence and logarithm rules now give the exact identity

$$
\log\frac{\Gamma(x+c)}{x^c\Gamma(x)}
=R(x+c)-R(x)+x\log(1+c/x)
+(c-\tfrac12)\log(1+c/x)-c.
$$

The two remainders have the same limit. Also $\log(1+c/x)\to0$ and the standard logarithmic limit gives $x\log(1+c/x)\to c$. Thus the logarithm of the ratio tends to zero. Positivity permits exponentiation, proving the ratio limit. Negative shifts and $c=0$ require no separate restriction beyond the eventual domain.

**Lean declarations:** `Rudin.Chapter08.Exercise30.logGamma_interpolation`, `Rudin.Chapter08.Exercise30.remainder_interpolation`, `Rudin.Chapter08.Exercise30.tendsto_logStirlingRemainder`, `Rudin.Chapter08.Exercise30.eventually_gamma_ratio_domain`, `Rudin.Chapter08.Exercise30.log_gamma_ratio_eq`, `Rudin.Chapter08.Exercise30.exercise30_gamma_ratio`.

<a id="r08e31"></a>
### 8.31 — A scaled polynomial integral

**Lean source:** [Exercise31.lean](../../Math/Rudin/Chapter08/Exercise31.lean).

**Inventory status:** Verified as stated.

**Statement.** For every natural $n$, the polynomial integral exists and has value

$$
I_n=\int_{-1}^{1}(1-x^2)^n\,dx
=\frac{\sqrt\pi\,\Gamma(n+1)}{\Gamma(n+3/2)}.
$$

This is also its Darboux and tagged Riemann value, including $n=0$. As $n\to\infty$ through positive integers,

$$
\sqrt n\,I_n\longrightarrow\sqrt\pi.
$$

The same limit holds for any sequence of literal tagged Riemann values of these integrands, and also when the sequence is indexed by all natural numbers.

**Proof.** The beta integral identity of Theorem 8.20 at the positive arguments $n+1,n+1$ gives

$$
\int_0^1t^n(1-t)^n\,dt
=\frac{\Gamma(n+1)^2}{\Gamma(2n+2)}.
$$

The integrand is a continuous polynomial, so integrability is established separately. The affine substitution $x=2t-1$ gives $I_n=2\cdot4^n\int_0^1t^n(1-t)^n\,dt$. Legendre's duplication formula at $n+1$, with all Gamma denominators positive, reduces this to the stated expression for $I_n$. Continuity on $[-1,1]$ also constructs both source Riemann values and identifies them with this integral; at $n=0$ the value is $2$.

For $n>0$, Gamma recurrence and $n^{3/2}=n\sqrt n$ yield

$$
\sqrt n\,I_n
=\sqrt\pi\left(\frac{\Gamma(n+3/2)}{n^{3/2}\Gamma(n)}\right)^{-1}.
$$

Exercise 30 with $c=3/2$, restricted to the natural-number sequence, makes the ratio tend to $1$. Its inverse also tends to $1$, proving the scaled limit. Omitting the single index zero gives the positive-integer formulation. Uniqueness and the proved Riemann-to-interval integral comparison identify any sequence of tagged values with $I_n$, so that formulation has the same limit.

**Lean declarations:** `Rudin.Chapter08.Exercise31.beta_integral_nat`, `Rudin.Chapter08.Exercise31.integral_affine_beta`, `Rudin.Chapter08.Exercise31.integral_eq_gamma`, `Rudin.Chapter08.Exercise31.integral_integrable`, `Rudin.Chapter08.Exercise31.integral_riemann_value`, `Rudin.Chapter08.Exercise31.scaled_integral_eq_ratio`, `Rudin.Chapter08.Exercise31.exercise31_scaled_integral_limit_nat`, `Rudin.Chapter08.Exercise31.exercise31_scaled_integral_limit`, `Rudin.Chapter08.Exercise31.exercise31_riemann_limit`.

<a id="chapter-09"></a>

## Chapter 9 — Functions of Several Variables

**Exercises:** [1](#r09e01) · [2](#r09e02) · [3](#r09e03) · [4](#r09e04) · [5](#r09e05) · [6](#r09e06) · [7](#r09e07) · [8](#r09e08) · [9](#r09e09) · [10](#r09e10) · [11](#r09e11) · [12](#r09e12) · [13](#r09e13) · [14](#r09e14) · [15](#r09e15) · [16](#r09e16) · [17](#r09e17) · [18](#r09e18) · [19](#r09e19) · [20](#r09e20) · [21](#r09e21) · [22](#r09e22) · [23](#r09e23) · [24](#r09e24) · [25](#r09e25) · [26](#r09e26) · [27](#r09e27) · [28](#r09e28) · [29](#r09e29) · [30](#r09e30) · [31](#r09e31)

<a id="r09e01"></a>
### 9.1 — Finite linear combinations form a vector space
**Lean source:** [Exercise01.lean](../../Math/Rudin/Chapter09/Exercise01.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $X$ be a real vector space and $S\subseteq X$ nonempty. The set of finite linear combinations of elements of $S$ is a vector subspace of $X$, with the inherited operations. The formal result applies more generally to a vector space over any field $K$.

**Proof.** Define

$$
V=\left\{\sum_{s\in T}c_s s:T\subseteq S\text{ finite},\ c_s\in K\right\}.
$$

Every element of $S$ belongs to $V$ as a one-term combination. The zero vector is the empty sum, or a one-term combination with coefficient zero, since $S$ is nonempty. If $x,y\in V$, choose finite sets supporting their combinations. Extend their coefficients by zero to the union of these sets. Adding the coefficients gives a finite combination representing $x+y$, so $x+y\in V$. For $\lambda\in K$, multiplying every coefficient in a representation of $x$ by $\lambda$ gives $\lambda x\in V$. In particular, $-x\in V$. The remaining vector-space identities are inherited from $X$.

The file also identifies this explicit set with the usual span: every finite combination lies in any subspace containing $S$, while the standard finite-combination description of the span gives the reverse inclusion. The submodule construction therefore has exactly $V$ as its carrier, not a larger set.

**Scope.** Empty sums are permitted. For the source's nonempty $S$, they add no new vector beyond its one-term combinations with coefficient zero.

**Lean declarations:** `exercise01`, `mem_finiteLinearCombinations_iff`.

<a id="r09e02"></a>
### 9.2 — Composition and inverses of linear maps

**Lean source:** [Exercise02.lean](../../Math/Rudin/Chapter09/Exercise02.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $X,Y,Z$ be vector spaces over a field $K$. If $A:X\to Y$ and $B:Y\to Z$ are linear, then $B\circ A$ is linear. If $A:X\to X$ is bijective, its inverse is linear and bijective, with inverse $A$. No finite-dimensional or nonzero-space assumption is needed.

**Proof.** For $x,y\in X$ and $c\in K$,

$$
B(A(x+y))=B(Ax)+B(Ay),\qquad B(A(cx))=cB(Ax).
$$

For the inverse claim, first take an ordinary function $g:X\to X$ with $gA=Ag=\operatorname{id}$. The identity $gA=\operatorname{id}$ makes $A$ injective. Applying $A$ to $g(x+y)$ and $g(x)+g(y)$ gives $x+y$ in both cases, so injectivity gives additivity of $g$. Applying $A$ to $g(cx)$ and $cg(x)$ gives $cx$ in both cases, so $g$ preserves scalar multiplication. The two inverse identities also make $g$ injective and surjective, and show that $A$ is its two-sided inverse. For bijective $A$, take the inverse function of its associated bijection and apply these results.

**Lean declarations:** `Rudin.Chapter09.exercise02_composition`, `Rudin.Chapter09.exercise02_inverse_linearity`, `Rudin.Chapter09.exercise02_inverse_invertibility`, `Rudin.Chapter09.exercise02_inverse`.

<a id="r09e03"></a>
### 9.3 — A trivial kernel implies injectivity

**Lean source:** [Exercise03.lean](../../Math/Rudin/Chapter09/Exercise03.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $A:X\to Y$ be linear between vector spaces over a field $K$. If $Ax=0$ implies $x=0$, then $A$ is injective. The assertion includes zero-dimensional spaces.

**Proof.** If $Ax=Ay$, linearity gives $A(x-y)=Ax-Ay=0$. The hypothesis gives $x-y=0$, hence $x=y$.

**Lean declarations:** `Rudin.Chapter09.exercise03`.

<a id="r09e04"></a>
### 9.4 — The kernel and range are vector subspaces

**Lean source:** [Exercise04.lean](../../Math/Rudin/Chapter09/Exercise04.lean).

**Inventory status:** Verified as stated.

**Statement.** For a linear map $A:X\to Y$ over any field $K$, the sets $\{x:Ax=0\}$ and $A(X)$ are vector subspaces of $X$ and $Y$, respectively, with the inherited operations. No dimension assumption is needed.

**Proof.** The kernel contains zero. If $Ax=Ay=0$, then $A(x+y)=0$, and $A(cx)=cAx=0$ for every scalar $c$. Thus the kernel is closed under addition and scalar multiplication. The range contains $A0=0$; sums and scalar multiples of range elements have the forms $Ax+Ay=A(x+y)$ and $cAx=A(cx)$. These closure properties make both sets subspaces, so their inherited operations satisfy the vector-space axioms. The formal proofs use the library kernel and range subspaces and identify their carriers with these exact sets.

**Lean declarations:** `Rudin.Chapter09.exercise04_kernel`, `Rudin.Chapter09.exercise04_range`.

<a id="r09e05"></a>
### 9.5 — Representing a linear functional by a vector

**Lean source:** [Exercise05.lean](../../Math/Rudin/Chapter09/Exercise05.lean).

**Inventory status:** Verified as stated.

**Statement.** For every real linear functional $A:\mathbb R^n\to\mathbb R$, there is a unique $y\in\mathbb R^n$ such that $Ax=x\cdot y$ for all $x$. With the Euclidean norm,

$$
\|A\|=\sup_{\|x\|\leq1}|Ax|=\|y\|.
$$

The result includes $n=0$ and the zero functional. Continuity of $A$ follows from finite dimension; it is not an additional assumption.

**Proof.** Let $e_i$ be the coordinate vectors and set $y_i=Ae_i$. Expanding $x=\sum_i x_i e_i$ gives

$$
Ax=\sum_i x_iAe_i=\sum_i x_i y_i=x\cdot y.
$$

Any other representing vector has the same $i$th coordinate by evaluation at $e_i$, which proves uniqueness. The resulting continuous linear functional is the inner-product functional defined by $y$. Its standard norm theorem gives the norm equality: Cauchy–Schwarz gives $|Ax|\leq\|x\|\|y\|$, and for $y\neq0$ evaluation at $y/\|y\|$ gives equality on the unit ball. If $y=0$, the functional and both norms are zero. This also treats dimension zero. The library closed-unit-ball supremum formula identifies this operator norm with the displayed supremum.

**Lean declarations:** `Rudin.Chapter09.exercise05Vector`, `Rudin.Chapter09.exercise05_representing_vector`, `Rudin.Chapter09.exercise05_uniqueness`, `Rudin.Chapter09.exercise05_existsUnique`, `Rudin.Chapter09.exercise05_norm`, `Rudin.Chapter09.exercise05_source_norm`.

<a id="r09e06"></a>
### 9.6 — Coordinate partials without continuity

**Lean source:** [Exercise06.lean](../../Math/Rudin/Chapter09/Exercise06.lean).

**Inventory status:** Verified as stated.

**Statement.** Define $f(0,0)=0$ and

$$
f(x,y)=\frac{xy}{x^2+y^2}\quad\text{for }(x,y)\neq(0,0).
$$

Both coordinate partial derivatives exist everywhere, but $f$ is not continuous at the origin. Away from the origin their values are

$$
D_1f(x,y)=\frac{y(y^2-x^2)}{(x^2+y^2)^2},\qquad
D_2f(x,y)=\frac{x(x^2-y^2)}{(x^2+y^2)^2}.
$$

At the origin both partial derivatives are zero.

**Proof.** For the first partial, fix $y$. If $y=0$, the function of $x$ is identically zero, so its derivative is zero at every $x$. If $y\neq0$, the denominator is positive and the quotient rule gives the first displayed formula. For the second partial, fix $x$. If $x=0$, the function of $y$ is identically zero; otherwise the quotient rule gives the second formula. This proves genuine one-variable derivative existence at every point, including both axes and the origin. Translating the coordinate parameter gives the equivalent derivatives along $p+te_j$ at $t=0$.

On the punctured diagonal, $f(t,t)=1/2$. Were $f$ continuous at the origin, its composition with the continuous curve $t\mapsto(t,t)$ would tend to $f(0,0)=0$. Its punctured limit is instead $1/2$, a contradiction.

**Lean declarations:** `Rudin.Chapter09.exercise06Function_zero`, `Rudin.Chapter09.exercise06_partial_one`, `Rudin.Chapter09.exercise06_partial_two`, `Rudin.Chapter09.exercise06_partials`, `Rudin.Chapter09.exercise06_diagonal`, `Rudin.Chapter09.exercise06_discontinuity`.

<a id="r09e07"></a>
### 9.7 — Bounded partial derivatives imply continuity

**Lean source:** [Exercise07.lean](../../Math/Rudin/Chapter09/Exercise07.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $E\subset\mathbb R^n$ be open. Suppose every coordinate partial derivative $p_i(x)=D_i f(x)$ exists on $E$, and for each $i$ there is a real bound $C_i$ with $|p_i(x)|\leq C_i$ for all $x\in E$. Then $f$ is continuous on $E$. The partial derivatives need not be continuous. A second formulation assumes one common nonnegative bound $C$.

**Proof.** First use ordinary coordinate space with the supremum norm. Fix $a\in E$ and choose an open cube $Q=\{x:\|x-a\|_\infty<r\}$ contained in $E$. On a coordinate line in this cube, the one-variable function is differentiable throughout its interval. The mean value inequality gives

$$
|f(x)-f(x_1,\ldots,x_{i-1},t,x_{i+1},\ldots,x_n)|\leq C|x_i-t|
$$

whenever both points lie in $Q$. Change the coordinates one at a time from $x$ to $y$. Each intermediate point remains in $Q$, and the triangle inequality gives

$$
|f(x)-f(y)|\leq\sum_{i=1}^n C|x_i-y_i|\leq nC\|x-y\|_\infty.
$$

The formal finite-coordinate estimate is proved by induction on the set of coordinates to be changed. Taking $y=a$ proves continuity; for example, $\delta=\min\{r,\varepsilon/(nC+1)\}$ is sufficient. The continuous coordinate equivalence transfers this result to Euclidean space. For separate coordinate bounds, choose $C=\sum_i|C_i|$, which dominates every partial derivative. Empty domains and $n=0$ are included, with empty sums interpreted as zero.

**Lean declarations:** `Rudin.Chapter09.coordinate_telescope`, `Rudin.Chapter09.continuousOn_of_bounded_coordinate_derivatives`, `Rudin.Chapter09.exercise07`, `Rudin.Chapter09.exercise07_of_coordinate_bounds`.

<a id="r09e08"></a>
### 9.8 — A derivative vanishes at an interior maximum

**Lean source:** [Exercise08.lean](../../Math/Rudin/Chapter09/Exercise08.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $E\subset\mathbb R^n$ be open and let $f:\mathbb R^n\to\mathbb R$ be differentiable on $E$. If $x\in E$ is a local maximum relative to $E$, then $f$ has the zero Fréchet derivative at $x$; in particular, $f'(x)=0$.

**Proof.** Since $E$ is a neighborhood of $x$, differentiability on $E$ gives ordinary differentiability at $x$, and the relative local maximum is an ordinary local maximum. Apply the standard stationarity theorem for a differentiable real function at a local extremum. This theorem forces its derivative to be zero: restriction to any line through $x$ has a local maximum and hence zero one-variable derivative. The conclusion asserts actual derivative existence with value zero, not merely a value assigned by a total derivative operator.

**Lean declarations:** `Rudin.Chapter09.exercise08`.

<a id="r09e09"></a>
### 9.9 — Zero derivative on a connected open set

**Lean source:** [Exercise09.lean](../../Math/Rudin/Chapter09/Exercise09.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $E\subset\mathbb R^n$ be open and preconnected, and let $f:\mathbb R^n\to\mathbb R^m$ be differentiable on $E$. If $f'(x)=0$ for every $x\in E$, then there is $c\in\mathbb R^m$ such that $f(x)=c$ for every $x\in E$. Both dimensions are arbitrary, and $E$ may be empty.

**Proof.** Apply the standard zero-derivative constancy theorem on an open preconnected set. Its mean value argument makes $f$ constant on each sufficiently small ball contained in $E$, since such a ball is convex and the derivative vanishes there. Thus $f$ is locally constant on $E$. Preconnectedness makes a locally constant function constant on a nonempty domain. For $E=\varnothing$, choose any vector, for example zero; the assertion is vacuous. Differentiability is essential to the stated hypotheses and is not replaced by the equation for the total derivative operator alone.

**Lean declarations:** `Rudin.Chapter09.exercise09`.

<a id="r09e10"></a>
### 9.10 — Independence of the first coordinate

**Lean source:** [Exercise10.lean](../../Math/Rudin/Chapter09/Exercise10.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $E\subset\mathbb R^{n+1}$ be open and convex. Suppose the first coordinate derivative of $f$ exists and equals zero everywhere on $E$. If $x,y\in E$ have the same coordinates other than the first, then $f(x)=f(y)$. Convexity can be replaced by the weaker requirement that every fiber parallel to the first coordinate axis is preconnected, allowing empty fibers. This weaker requirement is strictly weaker than convexity. Without a domain condition the conclusion can fail.

**Proof.** For a fixed $x$, write $L_x(t)$ for $x$ with its first coordinate replaced by $t$. The set $J_x=L_x^{-1}(E)$ is open. The coordinate derivative assumption says that $t\mapsto f(L_x(t))$ has derivative zero at every $t\in J_x$. If $J_x$ is preconnected, the one-variable zero-derivative theorem makes this function constant on $J_x$. The numbers $x_1$ and $y_1$ belong to this same fiber, which gives $f(x)=f(y)$. For convex $E$, each $J_x$ is convex, because $L_x$ preserves affine combinations, so it is preconnected.

For strict weakness, use $E=\{(x,y):y\neq0\}$. Each horizontal fiber is either all of $\mathbb R$ or empty, so the fiber condition holds. The midpoint of $(0,-1)$ and $(0,1)$ is missing, so $E$ is not convex.

For failure without the fiber condition, use the different open set $E=\{(x,y):x\neq0\}$ and define $f(x,y)=1$ for $x>0$ and $f(x,y)=0$ for $x\leq0$. On $E$ the function is locally constant along each horizontal line, so its first partial derivative exists and is zero. However, $(-1,0)$ and $(1,0)$ have the same second coordinate and different function values. The proved example is this disconnected open set; no horseshoe construction is needed.

**Lean declarations:** `Rudin.Chapter09.firstCoordinateLine`, `Rudin.Chapter09.exercise10_weaker_condition`, `Rudin.Chapter09.exercise10`, `Rudin.Chapter09.exercise10_weaker_not_convex`, `Rudin.Chapter09.exercise10_domain_counterexample`.

<a id="r09e11"></a>
### 9.11 — Gradient product and reciprocal rules

**Lean source:** [Exercise11.lean](../../Math/Rudin/Chapter09/Exercise11.lean).

**Inventory status:** Verified as stated.

**Statement.** If real functions $f,g$ on $\mathbb R^n$ are differentiable at $x$, then their product has gradient

$$
\nabla(fg)(x)=f(x)\nabla g(x)+g(x)\nabla f(x).
$$

If $f$ is differentiable at $x$ and $f(x)\neq0$, then its reciprocal has gradient

$$
\nabla(1/f)(x)=-\frac{1}{f(x)^2}\nabla f(x).
$$

Both assertions include existence of the indicated gradient at $x$.

**Proof.** Represent the derivatives of $f$ and $g$ by their gradients using the real inner product. The Fréchet product rule gives $D(fg)(x)=f(x)Dg(x)+g(x)Df(x)$. Linearity of the inner-product representation gives the first gradient. For the reciprocal, compose $f$ with the one-variable function $u\mapsto u^{-1}$, whose derivative at a nonzero $u$ is $-u^{-2}$. The chain rule and the same inner-product representation give the second formula. The nonzero assumption is needed only at the point in question.

**Lean declarations:** `Rudin.Chapter09.exercise11_product`, `Rudin.Chapter09.exercise11_reciprocal`.

<a id="r09e12"></a>
### 9.12 — A torus, its coordinate extrema, and an irrational winding

**Lean source:** [Exercise12.lean](../../Math/Rudin/Chapter09/Exercise12.lean).

**Inventory status:** Verified as stated.

**Statement.** Fix $0<a<b$ and define

$$
F(s,t)=((b+a\cos s)\cos t,(b+a\cos s)\sin t,a\sin s),\qquad (s,t)\in\mathbb R^2.
$$

Its range is the compact ring torus

$$
K=\{(x,y,z):(\sqrt{x^2+y^2}-b)^2+z^2=a^2\}.
$$

For the first coordinate $F_1$, the points of $K$ whose entire fibers have zero parameter gradient are exactly

$$
(b+a,0,0),\quad (-(b+a),0,0),\quad (b-a,0,0),\quad (-(b-a),0,0).
$$

These four points are distinct. At every parameter in their respective fibers, the first is a global and local maximum of $F_1$, the second a global and local minimum, and the last two are saddles. There are no other local maxima or minima of $F_1$. The saddle assertion also holds for the first coordinate on $K$ with its relative topology.

For $F_3$, the fibers with zero gradient are exactly the two circles

$$
x^2+y^2=b^2,\qquad z=a\ \text{or}\ z=-a.
$$

The upper circle gives all local maxima, which are global maxima; the lower circle gives all local minima, which are global minima. Finally, if $\lambda$ is irrational, $g(t)=F(t,\lambda t)$ is injective and has range dense in $K$. Its speed satisfies

$$
\|g'(t)\|^2=a^2+\lambda^2(b+a\cos t)^2.
$$

Here a fiber means the full inverse image of a point, not a chosen inverse function.

**Proof.** The radius $r=b+a\cos s$ is strictly positive because $b>a$. The identity $x^2+y^2=r^2$ and $\sin^2s+\cos^2s=1$ show that $F(s,t)\in K$. Conversely, for $(x,y,z)\in K$, set $r=\sqrt{x^2+y^2}$. The surface equation and $b>a$ imply $r>0$. The pairs $((r-b)/a,z/a)$ and $(x/r,y/r)$ lie on the unit circle. Choose angles $s,t$ with these cosine and sine values; then $F(s,t)=(x,y,z)$. Periodicity in both parameters shows that the closed square $[0,2\pi]^2$ has the full range. Its continuous image is compact, proving compactness of $K$.

Differentiation gives

$$
\nabla F_1(s,t)=(-a\sin s\cos t,-(b+a\cos s)\sin t),\qquad
\nabla F_3(s,t)=(a\cos s,0).
$$

The first gradient vanishes exactly when $\sin s=\sin t=0$. Indeed, its second component first forces $\sin t=0$; then $\cos t\neq0$ and the first forces $\sin s=0$. The four choices of the corresponding cosine signs give exactly the four displayed points. Conversely, membership in any of those four fibers forces these sine values to vanish, using the zero second and third coordinates and positivity of the radius. The inequalities $0<a<b$ make all four first coordinates distinct. The third gradient vanishes exactly when $\cos s=0$, or equivalently $\sin s=\pm1$. Thus $z=\pm a$, and the torus equation reduces to $x^2+y^2=b^2$. These arguments apply to every parameter in each fiber.

The bounds $-(b+a)\leq F_1\leq b+a$ and $-a\leq F_3\leq a$ prove the asserted global extrema. At an inner equatorial point, $\cos s=-1$ and $\cos t=\pm1$. For small $h>0$, changing $s$ to $s+h$ changes the radial factor from $b-a$ to $b-a\cos h$, which is larger. Changing $t$ to $t+h$ instead multiplies the first coordinate by $\cos h<1$. According to the sign of $\cos t$, these two perturbations give opposite strict inequalities. They stay in any prescribed parameter neighborhood for sufficiently small $h$. Hence both inner points are saddles and neither is an extremum. Continuity of $F$ transfers the two strict inequalities to points of $K$ in every ambient neighborhood of the corresponding surface point.

Every parameter local extremum has zero gradient. The finite critical-point list therefore reduces the first-coordinate classification to the four cases already considered. At the outer negative point, a small change in $t$ increases the first coordinate, so it is not a maximum; at the outer positive point the same change decreases it, so it is not a minimum. For the third coordinate, at $\cos s=0$ a change from $s$ to $s+h$ multiplies its value by $\cos h$. This excludes a minimum on the upper circle and a maximum on the lower circle, and proves the complete classifications.

To analyze fibers, equality of two torus values first determines the positive radial factors from $x^2+y^2$. It then determines $\cos s,\sin s$ and, after division by that radius, $\cos t,\sin t$. Equality of both sine and cosine is equality modulo $2\pi$. Consequently,

$$
F(s,t)=F(u,v)\quad\Longleftrightarrow\quad
u=s+2\pi k,\quad v=t+2\pi m\quad\text{for some }k,m\in\mathbb Z.
$$

For $g(x)=g(y)$, the fiber equations give $y-x=2\pi k$ and $\lambda(y-x)=2\pi m$. Thus $\lambda k=m$. Irrationality forces $k=0$, and then $x=y$.

For density, fix a target $F(s,t)$. At parameters $s+2\pi n$, with $n\in\mathbb Z$, the first torus angle is unchanged modulo a full turn, while the second angle is $\lambda s+2\pi n\lambda$. The standard irrational-rotation density theorem makes these second angles dense in the circle. The continuous circle parametrization therefore places $F(s,t)$ in the closure of the winding range. The reverse inclusion follows because $K$ is closed and contains the winding range.

Finally, the coordinate product and chain rules give

$$
g'(t)=\bigl(-a\sin t\cos(\lambda t)-\lambda R\sin(\lambda t),\ -a\sin t\sin(\lambda t)+\lambda R\cos(\lambda t),\ a\cos t\bigr),\qquad R=b+a\cos t.
$$

Squaring the Euclidean norm cancels the cross terms. The sine-square and cosine-square identities give the stated speed formula. The derivative and speed formulas themselves hold for all real $a,b,\lambda,t$; irrationality is needed for injectivity and density, not for differentiation.

**Lean declarations:** `Rudin.Chapter09.Exercise12.range_eq_surface`, `Rudin.Chapter09.Exercise12.fundamental_square`, `Rudin.Chapter09.Exercise12.compact_surface`, `Rudin.Chapter09.Exercise12.first_hasGradientAt`, `Rudin.Chapter09.Exercise12.third_hasGradientAt`, `Rudin.Chapter09.Exercise12.first_gradient_zero`, `Rudin.Chapter09.Exercise12.third_gradient_zero`, `Rudin.Chapter09.Exercise12.first_critical`, `Rudin.Chapter09.Exercise12.four_distinct`, `Rudin.Chapter09.Exercise12.first_critical_count`, `Rudin.Chapter09.Exercise12.third_critical`, `Rudin.Chapter09.Exercise12.third_critical_circles`, `Rudin.Chapter09.Exercise12.first_maximum`, `Rudin.Chapter09.Exercise12.first_minimum`, `Rudin.Chapter09.Exercise12.first_saddles`, `Rudin.Chapter09.Exercise12.first_surface_saddles`, `Rudin.Chapter09.Exercise12.first_local_max_iff`, `Rudin.Chapter09.Exercise12.first_local_min_iff`, `Rudin.Chapter09.Exercise12.third_maximum`, `Rudin.Chapter09.Exercise12.third_minimum`, `Rudin.Chapter09.Exercise12.third_local_max_iff`, `Rudin.Chapter09.Exercise12.third_local_min_iff`, `Rudin.Chapter09.Exercise12.fiber_trig`, `Rudin.Chapter09.Exercise12.fibers`, `Rudin.Chapter09.Exercise12.winding_injective`, `Rudin.Chapter09.Exercise12.winding_closure`, `Rudin.Chapter09.Exercise12.winding_hasDerivAt`, `Rudin.Chapter09.Exercise12.speed`.

<a id="r09e13"></a>
### 9.13 — Velocity is tangent to the unit sphere

**Lean source:** [Exercise13.lean](../../Math/Rudin/Chapter09/Exercise13.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $f:\mathbb R\to\mathbb R^3$ be differentiable and satisfy $\|f(t)\|=1$ for all $t$. Then $f'(t)\cdot f(t)=0$. In geometric terms, for every real $s$ the point $f(t)+sf'(t)$ lies in the affine tangent plane

$$
T_{f(t)}=\{q:(q-f(t))\cdot f(t)=0\}.
$$

Zero velocity is allowed, and $f(t)+s0$ also lies in this plane.

**Proof.** The identity $f(t)\cdot f(t)=1$ has derivative zero. The inner-product product rule gives $f'(t)\cdot f(t)+f(t)\cdot f'(t)=0$. Symmetry of the real inner product makes this $2f'(t)\cdot f(t)=0$. Thus the velocity is perpendicular to the radius. Substituting $q=f(t)+sf'(t)$ into the plane equation gives $s(f'(t)\cdot f(t))=0$. The same substitution for zero velocity gives zero directly. The norm hypothesis also places $f(t)$ on the unit sphere.

**Lean declarations:** `Rudin.Chapter09.exercise13_orthogonality`, `Rudin.Chapter09.sphereTangentPlane`, `Rudin.Chapter09.exercise13_geometry`.

<a id="r09e14"></a>
### 9.14 — Differentiability along curves without a total derivative

**Lean source:** [Exercise14.lean](../../Math/Rudin/Chapter09/Exercise14.lean).

**Inventory status:** Verified as stated.

**Statement.** Define $f(0,0)=0$ and $f(x,y)=x^3/(x^2+y^2)$ elsewhere. Its coordinate partials exist everywhere and have uniform absolute bounds $3$ and $2$, respectively. Off the origin they are

$$
A(x,y)=\frac{x^2(x^2+3y^2)}{(x^2+y^2)^2},\qquad
B(x,y)=-\frac{2x^3y}{(x^2+y^2)^2}.
$$

At the origin the partials are $1$ and $0$. The function is continuous on the whole plane. For every direction $u$, the function $t\mapsto f(tu)$ has derivative $f(u)$ at zero; for $\|u\|=1$, this derivative has absolute value at most $1$.

More strongly than the source's specified initial conditions on a curve, every differentiable $\gamma:\mathbb R\to\mathbb R^2$ makes $f\circ\gamma$ differentiable on all of $\mathbb R$. At any parameter $a$,

$$
(f\circ\gamma)'(a)=
\begin{cases}
f(\gamma'(a)),&\gamma(a)=0,\\
A(\gamma(a))\gamma_1'(a)+B(\gamma(a))\gamma_2'(a),&\gamma(a)\neq0.
\end{cases}
$$

If $\gamma$ is $C^1$, so is $f\circ\gamma$. These claims include repeated visits to zero and visits with zero velocity. Nevertheless, $f$ is not Fréchet differentiable at the origin.

**Proof.** For nonzero $p=(x,y)$, the denominator is positive. Algebra gives homogeneity $f(sp)=sf(p)$ for every real $s$, including $s=0$ and $p=0$. Also,

$$
|f(x,y)|=\frac{|x|x^2}{x^2+y^2}\leq|x|.
$$

This bound proves continuity at zero by squeezing, and the quotient formula proves continuity elsewhere.

At a zero of a differentiable curve, put $v=\gamma'(a)$. For $t\neq a$, homogeneity gives

$$
\frac{f(\gamma(t))-f(\gamma(a))}{t-a}=f\left(\frac{\gamma(t)-\gamma(a)}{t-a}\right).
$$

The vector difference quotient tends to $v$, so continuity of $f$ gives the derivative $f(v)$. This proof does not require $v\neq0$. Applying it to $\gamma(t)=tu$ proves all directional derivatives. For unit $u$, the bound $|f(u)|\leq|u_1|\leq\|u\|=1$ gives the required estimate.

Away from zero, the quotient and chain rules give the stated coefficients $A,B$ and the curve derivative formula. Direct estimates give $|A|\leq3$ and $|B|\leq2$: the first follows by comparing $x^2(x^2+3y^2)$ with $3(x^2+y^2)^2$; for the second use $|x||y|\leq x^2+y^2$ and $x^2\leq x^2+y^2$. At zero, the coordinate restrictions are $f(t,0)=t$ and $f(0,t)=0$, which give partials $1,0$ and satisfy the same bounds. Thus the formulas for curves cover every parameter, and the bounded partials also meet the continuity criterion of Exercise 9.7. The direct continuity proof above is the one used in this file.

For the $C^1$ assertion, $A$ and $B$ are continuous away from zero and unchanged by nonzero scalar multiplication. They satisfy the Euler identity

$$
A(p)p_1+B(p)p_2=f(p).
$$

The rational definitions assign $A(0)=B(0)=0$; these assigned coefficient values are not the pair of actual partials at zero. The identity and uniform bounds still hold there. At a parameter with $\gamma(a)\neq0$, the off-zero curve formula and continuity of $\gamma,\gamma'$ prove continuity of $(f\circ\gamma)'$. If $\gamma(a)=\gamma'(a)=0$, use the bound, valid for all $t$,

$$
|(f\circ\gamma)'(t)|\leq3|\gamma_1'(t)|+2|\gamma_2'(t)|.
$$

Its right side tends to zero, which is the derivative at $a$. If $\gamma(a)=0$ but $v=\gamma'(a)\neq0$, extend $w(t)=\gamma(t)/(t-a)$ by $w(a)=v$. Differentiability makes $w$ continuous at $a$ and nonzero nearby. For $t\neq a$ nearby, $\gamma(t)=(t-a)w(t)$, so scale invariance rewrites the derivative as $A(w(t))\gamma_1'(t)+B(w(t))\gamma_2'(t)$. Its limit is $A(v)v_1+B(v)v_2=f(v)$ by the Euler identity. The same formula agrees at $a$. This proves continuity of the derivative in every case.

Finally, if a total derivative $L$ existed at zero, comparison with every line derivative would give $L(u)=f(u)$ for all $u$. For the coordinate vectors, $f(e_1)=1$ and $f(e_2)=0$, whereas $f(e_1+e_2)=1/2$. This contradicts additivity of $L$.

**Lean declarations:** `Rudin.Chapter09.exercise14_value_zero`, `Rudin.Chapter09.exercise14_homogeneous`, `Rudin.Chapter09.exercise14_bound`, `Rudin.Chapter09.exercise14_partials`, `Rudin.Chapter09.exercise14_A_bound`, `Rudin.Chapter09.exercise14_B_bound`, `Rudin.Chapter09.exercise14_continuous`, `Rudin.Chapter09.exercise14_directional`, `Rudin.Chapter09.exercise14_unit_directional`, `Rudin.Chapter09.exercise14_curve_at_zero`, `Rudin.Chapter09.exercise14_curve_off_zero`, `Rudin.Chapter09.exercise14_curve_differentiable`, `Rudin.Chapter09.exercise14_coefficients_scale`, `Rudin.Chapter09.exercise14_euler`, `Rudin.Chapter09.exercise14_coefficients_continuous`, `Rudin.Chapter09.exercise14_curve_deriv_bound`, `Rudin.Chapter09.exercise14_curve_C1`, `Rudin.Chapter09.exercise14_not_differentiable`.

<a id="r09e15"></a>
### 9.15 — Strict minima on lines but not in the plane

**Lean source:** [Exercise15.lean](../../Math/Rudin/Chapter09/Exercise15.lean).

**Inventory status:** Verified as stated.

**Statement.** Define $f(0,0)=0$ and, away from zero,

$$
f(x,y)=x^2+y^2-2x^2y-\frac{4x^6y^2}{(x^4+y^2)^2}.
$$

Then $f$ is continuous on the plane. For every unit pair $a^2+b^2=1$, the line restriction $g(t)=f(ta,tb)$ is differentiable at every real parameter and satisfies

$$
g(0)=g'(0)=0,\qquad g''(0)=2.
$$

It has a strict local minimum at zero. In particular, these assertions hold for $a=\cos\theta,b=\sin\theta$ for every real $\theta$, including both endpoints of $[0,2\pi]$. However, $f(x,x^2)=-x^4$ for all real $x$, and zero is not a local minimum in the plane.

**Proof.** Expanding the nonnegative square $(x^4-y^2)^2$ gives

$$
4x^4y^2\leq(x^4+y^2)^2.
$$

For a nonzero point the denominator is positive. Multiplication by $x^2$ and division by its square give

$$
0\leq\frac{4x^6y^2}{(x^4+y^2)^2}\leq x^2.
$$

The rational term is assigned zero at the origin, where the same bound holds. Squeezing makes it continuous there; the quotient rule for continuity applies away from zero. The remaining polynomial terms are continuous, proving continuity of $f$.

For a unit pair, write $g(t)=t^2k(t)$. If $b=0$, then $a^2=1$ and $g(t)=t^2$, so take $k=1$. If $b\neq0$, cancellation for $t\neq0$, with direct checking at $t=0$, gives

$$
k(t)=1-2a^2bt-\frac{4a^6b^2t^2}{(a^4t^2+b^2)^2}.
$$

Its denominator is positive for all $t$, so $k$ is $C^2$ and $k(0)=1$. The product rule gives $g'(t)=2tk(t)+t^2k'(t)$ at every parameter. Differentiating this expression at zero gives $g''(0)=2k(0)=2$, and $g'(0)=g(0)=0$. Since $k$ is positive in a neighborhood of zero, $g(t)=t^2k(t)>0=g(0)$ for all sufficiently small nonzero $t$, proving strict local minimality. The trigonometric unit identity gives every angle case without an endpoint restriction.

Direct substitution on the parabola gives $f(x,x^2)=-x^4$ when $x\neq0$, and both sides vanish when $x=0$. The continuous curve $x\mapsto(x,x^2)$ tends to the origin, but its nonzero points have negative values. A planar local minimum would force these values to be nonnegative for all sufficiently small $x$, which is impossible.

**Lean declarations:** `Rudin.Chapter09.exercise15_zero`, `Rudin.Chapter09.exercise15_inequality`, `Rudin.Chapter09.exercise15_rational_bound`, `Rudin.Chapter09.exercise15_continuous`, `Rudin.Chapter09.exercise15_line_factor`, `Rudin.Chapter09.exercise15_factor_jet`, `Rudin.Chapter09.exercise15_line_derivatives`, `Rudin.Chapter09.exercise15_angles`, `Rudin.Chapter09.exercise15_line_strict_minimum`, `Rudin.Chapter09.exercise15_angle_strict_minimum`, `Rudin.Chapter09.exercise15_curved_values`, `Rudin.Chapter09.exercise15_no_minimum`.

<a id="r09e16"></a>
### 9.16 — An invertible derivative without local injectivity

**Lean source:** [Exercise16.lean](../../Math/Rudin/Chapter09/Exercise16.lean).

**Inventory status:** Verified as stated.

**Statement.** Define $f(0)=0$ and $f(x)=x+2x^2\sin(1/x)$ for $x\neq0$. Then $f$ is differentiable on $\mathbb R$, $f'(0)=1$, and

$$
f'(x)=1+4x\sin(1/x)-2\cos(1/x)\quad(x\neq0).
$$

On $(-1,1)$, $|f'(x)|\leq7$. Nevertheless, $f$ is not injective on any neighborhood of zero, despite its invertible derivative at zero.

**Proof.** For $x\neq0$ the difference quotient at zero is $1+2x\sin(1/x)$. Since $|x\sin(1/x)|\leq|x|$, this tends to $1$. At nonzero $x$, the product and chain rules give the displayed derivative, so $f$ is differentiable everywhere. For $0<|x|<1$, the bounds $|\sin u|,|\cos u|\leq1$ give $|f'(x)|\leq1+4|x|+2\leq7$. At zero its derivative is $1$, which satisfies the same bound.

Let

$$
x_n=\frac{1}{2\pi(n+1)},\qquad n=0,1,2,\ldots.
$$

These positive points tend to zero, and their reciprocal angles have sine zero and cosine one. Thus $f'(x_n)=-1$. Suppose $f$ were injective on some interval $(-r,r)$, $r>0$. Since differentiability makes it continuous, the standard theorem for continuous injective functions on an interval says it is strictly increasing or strictly decreasing there. In the increasing case, its derivative must be nonnegative at interior points; some $x_n\in(-r,r)$ contradicts this. In the decreasing case its derivative at zero must be nonpositive, contradicting $f'(0)=1$. Hence it is not injective on any such interval. Every neighborhood of zero contains one, so injectivity fails on every neighborhood. The same derivative sequence shows why derivative continuity at zero, required by the inverse function theorem, is absent here.

**Lean declarations:** `Rudin.Chapter09.exercise16_source`, `Rudin.Chapter09.exercise16_zero`, `Rudin.Chapter09.exercise16_derivative_at_zero`, `Rudin.Chapter09.exercise16_derivative_nonzero`, `Rudin.Chapter09.exercise16_differentiable`, `Rudin.Chapter09.exercise16_bounded_derivative`, `Rudin.Chapter09.exercise16Point_pos`, `Rudin.Chapter09.exercise16Point_limit`, `Rudin.Chapter09.exercise16Point_derivative`, `Rudin.Chapter09.exercise16_not_injOn_interval`, `Rudin.Chapter09.exercise16_not_locally_injective`.

<a id="r09e17"></a>
### 9.17 — The exponential map of the plane

**Lean source:** [Exercise17.lean](../../Math/Rudin/Chapter09/Exercise17.lean).

**Inventory status:** Verified as stated.

**Statement.** For $F(x,y)=(e^x\cos y,e^x\sin y)$, the range is $\mathbb R^2\setminus\{0\}$. The map is locally injective everywhere but is not globally injective. At $a=(0,\pi/3)$, put $b=F(a)=(1/2,\sqrt3/2)$. A local inverse taking $b$ to $a$ is

$$
G(w)=(\log|w|,\operatorname{Arg}w),
$$

with principal argument in $(-\pi,\pi)$. Its derivative and the forward derivative are

$$
F'(a)=\begin{pmatrix}1/2&-\sqrt3/2\\\sqrt3/2&1/2\end{pmatrix},\qquad
G'(b)=\begin{pmatrix}1/2&\sqrt3/2\\-\sqrt3/2&1/2\end{pmatrix}=F'(a)^{-1}.
$$

Each horizontal line $y=c$ maps onto the open ray $\{r(\cos c,\sin c):r>0\}$; each vertical line $x=c$ maps onto the circle of radius $e^c$.

**Proof.** Identify the Euclidean plane with $\mathbb C$. Then $F(z)=\exp z$, and its real derivative sends $h$ to $e^zh$. In real coordinates its matrix is

$$
\begin{pmatrix}e^x\cos y&-e^x\sin y\\e^x\sin y&e^x\cos y\end{pmatrix},
$$

whose determinant is $e^{2x}>0$. The inverse function theorem gives local injectivity. Global injectivity fails because $F(0)=F(2\pi i)$. The exponential never vanishes, and every nonzero $w$ is $\exp(\log w)$, proving the range claim.

On the strip $-\pi<\operatorname{Im}z<\pi$, the exponential and principal logarithm are continuous inverse maps onto the slit plane. This strip contains $a$, so this is an actual inverse branch near $b$, not just a right inverse. The logarithm derivative is multiplication by $b^{-1}=1/2-i\sqrt3/2$. The displayed matrices therefore represent the actual real derivatives; multiplication in either order gives the identity. Finally, $F(x+ic)=e^xe^{ic}$, and $e^x$ ranges over all positive numbers. For $F(c+iy)$ the norm is $e^c$, and the argument runs around the whole circle.

**Lean declarations:** `Rudin.Chapter09.exercise17_coordinates`, `Rudin.Chapter09.exercise17_euclidean_norm`, `Rudin.Chapter09.exercise17_range`, `Rudin.Chapter09.exercise17_hasFDerivAt`, `Rudin.Chapter09.exercise17_matrix_action`, `Rudin.Chapter09.exercise17_jacobian`, `Rudin.Chapter09.exercise17_jacobian_ne_zero`, `Rudin.Chapter09.exercise17_locally_injective`, `Rudin.Chapter09.exercise17_not_injective`, `Rudin.Chapter09.exercise17_inverse_formula`, `Rudin.Chapter09.exercise17_inverse_branch`, `Rudin.Chapter09.exercise17_inverse_value`, `Rudin.Chapter09.exercise17_b_value`, `Rudin.Chapter09.exercise17_forward_matrix`, `Rudin.Chapter09.exercise17_inverse_hasFDerivAt`, `Rudin.Chapter09.exercise17_inverse_matrix_action`, `Rudin.Chapter09.exercise17_inverse_identity`, `Rudin.Chapter09.exercise17_inverse_eq_matrix_inv`, `Rudin.Chapter09.exercise17_horizontal_image`, `Rudin.Chapter09.exercise17_vertical_image`.

<a id="r09e18"></a>
### 9.18 — The square map and its singular point

**Lean source:** [Exercise18.lean](../../Math/Rudin/Chapter09/Exercise18.lean).

**Inventory status:** Verified as stated.

**Statement.** For $F(x,y)=(x^2-y^2,2xy)$, the range is all of $\mathbb R^2$. Its derivative matrix and determinant are

$$
F'(x,y)=\begin{pmatrix}2x&-2y\\2y&2x\end{pmatrix},\qquad \det F'(x,y)=4(x^2+y^2).
$$

It is locally injective exactly away from zero, and it is not globally injective. For $a=(0,\pi/3)$ and $b=(-(\pi/3)^2,0)$, an inverse branch, in complex notation, is

$$
G(w)=i\exp\bigl(\tfrac12\log(-w)\bigr),\qquad w\notin[0,\infty).
$$

This branch takes values in the upper half-plane and satisfies $G(b)=a$. The derivative matrices are

$$
F'(a)=\begin{pmatrix}0&-2\pi/3\\2\pi/3&0\end{pmatrix},\qquad
G'(b)=\begin{pmatrix}0&3/(2\pi)\\-3/(2\pi)&0\end{pmatrix}=F'(a)^{-1}.
$$

Writing image coordinates as $(u,v)$, the image of $y=c\ne0$ is $u=(v/(2c))^2-c^2$, and that of $x=c\ne0$ is $u=c^2-(v/(2c))^2$. The horizontal axis maps onto $v=0$, $u\ge0$; the vertical axis maps onto $v=0$, $u\le0$.

**Proof.** Here $F(z)=z^2$, with real derivative $h\mapsto2zh$, giving the matrix and determinant. For any nonzero $w$, the formula $i\exp(\log(-w)/2)$ has square $w$ by $\exp(\log(-w))=-w$, even outside the continuous branch domain; zero is the square of zero. This proves surjectivity. The inverse function theorem applies at every nonzero $z$. At zero, every neighborhood contains a small nonzero real number and its negative, which have the same square. The pair $1,-1$ also disproves global injectivity.

If $-w$ is in the slit plane, its principal argument lies strictly between $-\pi$ and $\pi$. Thus $\cos(\operatorname{Arg}(-w)/2)>0$, and $G(w)$ has positive imaginary part. Squaring is injective on the upper half-plane: equal squares imply equality or opposite values, and two upper-half-plane points cannot be opposites. It follows that $G(F(z))=z$ there. These open sets give a continuous two-sided branch. The inverse derivative is multiplication by $(2a)^{-1}=-3i/(2\pi)$, which gives the stated matrix; both matrix products are the identity.

On a horizontal line, $u=x^2-c^2$ and $v=2cx$; when $c\ne0$, eliminating $x$ gives the whole stated parabola. The vertical-line calculation is the same with the sign reversed. For $c=0$, squares attain exactly the indicated closed half-axes, including the origin.

**Lean declarations:** `Rudin.Chapter09.exercise18_coordinates`, `Rudin.Chapter09.exercise18_range`, `Rudin.Chapter09.exercise18_hasFDerivAt`, `Rudin.Chapter09.exercise18_matrix_action`, `Rudin.Chapter09.exercise18_jacobian`, `Rudin.Chapter09.exercise18_jacobian_zero_iff`, `Rudin.Chapter09.exercise18_locally_injective_iff`, `Rudin.Chapter09.exercise18_not_injOn_nhds_zero`, `Rudin.Chapter09.exercise18_not_injective`, `Rudin.Chapter09.exercise18_inverse_branch`, `Rudin.Chapter09.exercise18_inverse_value`, `Rudin.Chapter09.exercise18_b_value`, `Rudin.Chapter09.exercise18_forward_matrix`, `Rudin.Chapter09.exercise18_inverse_hasFDerivAt`, `Rudin.Chapter09.exercise18_inverse_matrix_action`, `Rudin.Chapter09.exercise18_inverse_identity`, `Rudin.Chapter09.exercise18_inverse_eq_matrix_inv`, `Rudin.Chapter09.exercise18_horizontal_image`, `Rudin.Chapter09.exercise18_vertical_image`, `Rudin.Chapter09.exercise18_real_axis_image`, `Rudin.Chapter09.exercise18_imaginary_axis_image`.

<a id="r09e19"></a>
### 9.19 — Local graphs of two solution branches

**Lean source:** [Exercise19.lean](../../Math/Rudin/Chapter09/Exercise19.lean).

**Inventory status:** Verified as stated.

**Statement.** The solutions of

$$
3x+y-z+u^2=0,\qquad x-y+2z+u=0,\qquad 2x+2y-3z+2u=0
$$

are exactly

$$
u\in\{0,3\},\qquad x=-z/4-u,\qquad y=7z/4.
$$

Near every solution $(x_0,y_0,z_0,u_0)$, the full solution set is a unique smooth graph over any one of $x,y,z$, but not over $u$. Solvability here is local to a branch; it is not global uniqueness across the two lines.

**Proof.** Linear elimination gives $x=-z/4-u$ and $y=7z/4$; substitution leaves $u(u-3)=0$. Conversely, each of these two choices satisfies all three equations. In the open band $|u-u_0|<1$, the other branch is excluded. All solutions in that band therefore have each of the following equivalent descriptions:

$$
(x,y,z,u)=(-z/4-u_0,7z/4,z,u_0),
$$

$$
(x,y,z,u)=(-y/7-u_0,y,4y/7,u_0),
$$

$$
(x,y,z,u)=(x,-7(x+u_0),-4(x+u_0),u_0).
$$

These maps are affine, hence smooth on the open parameter domain $\mathbb R$. Their identities characterize all solutions in the band, so they give local uniqueness as well as existence. To disprove a graph over $u$, vary $x$ slightly in the last formula. Continuity puts a distinct such solution in every prescribed neighborhood of the base solution, while $u$ remains $u_0$. Thus failure follows from actual multiple solutions in the same fiber, not just from a vanishing Jacobian minor.

**Lean declarations:** `Rudin.Chapter09.exercise19_classification`, `Rudin.Chapter09.exercise19_solve_in_z`, `Rudin.Chapter09.exercise19_solve_in_y`, `Rudin.Chapter09.exercise19_solve_in_x`, `Rudin.Chapter09.exercise19_local_graphs`, `Rudin.Chapter09.exercise19_smooth_graphs`, `Rudin.Chapter09.exercise19_failure_in_u`.

<a id="r09e20"></a>
### 9.20 — Geometry of the scalar implicit function theorem

**Lean source:** [Exercise20.lean](../../Math/Rudin/Chapter09/Exercise20.lean).

**Inventory status:** Verified as stated.

**Statement.** Suppose $f$ is $C^1$ near $(a,b)\in\mathbb R^2$, $f(a,b)=0$, and $D_1f(a,b)\ne0$. The nearby zero set is the unique $C^1$ graph $x=g(y)$, with $g(b)=a$ and

$$
g'(b)=-\frac{D_2f(a,b)}{D_1f(a,b)}.
$$

The coordinate change $H(x,y)=(f(x,y),y)$ maps this local zero graph onto a segment of the vertical line with first coordinate zero. The same construction is proved for $y$ in any real Banach space $Y$, with derivative $g'(b)v=-L(0,v)/L(1,0)$, where $L=f'(a,b)$.

**Proof.** Split the differential as $L(h,v)=L(1,0)h+L(0,v)$. The derivative of $H$ sends $(h,v)$ to $(L(h,v),v)$ and is invertible, with inverse

$$
(s,v)\longmapsto\left(\frac{s-L(0,v)}{L(1,0)},v\right).
$$

Apply the $C^1$ inverse function theorem at $(a,b)$. Its open source and target contain $(a,b)$ and $(0,b)$, respectively. For $y$ in a sufficiently small open neighborhood $W$ of $b$, define $g(y)$ to be the first coordinate of $H^{-1}(0,y)$. The second coordinate is $y$, so $f(g(y),y)=0$. Injectivity of the local coordinate change proves that every zero in its source with $y\in W$ has $x=g(y)$. Its inverse is $C^1$, and evaluating its derivative on $(0,v)$ gives the derivative formula. In the scalar case, restriction of the genuine differential to the two coordinate lines identifies its coefficients with the two partial derivatives. This also explains the graphical proof: invert the coordinate change and pull back the zero line, with uniqueness only inside the chosen local source.

**Lean declarations:** `Rudin.Chapter09.scalarImplicitGraph_exists`, `Rudin.Chapter09.exercise20_graph`, `Rudin.Chapter09.exercise20_partials`, `Rudin.Chapter09.exercise20_proof_graph`.

<a id="r09e21"></a>
### 9.21 — A cubic with a line and an ellipse of zeros

**Lean source:** [Exercise21.lean](../../Math/Rudin/Chapter09/Exercise21.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $f(x,y)=2x^3-3x^2+2y^3+3y^2$. Its stationary points are $(0,0)$, $(0,-1)$, $(1,0)$, and $(1,-1)$. Its only local minimum is the strict minimum $(1,0)$; its only local maximum is the strict maximum $(0,-1)$. The other two stationary points are saddles. Its zero set is exactly

$$
S=\{y=-x\}\ \cup\ \{(x+y)^2+3(x-y-1)^2=3\}.
$$

The ellipse has $-1/2\le x\le3/2$, with branches

$$
y=\frac{2x-3\pm\sqrt{9+12x-12x^2}}4.
$$

The line and ellipse intersect exactly at $(0,0)$ and $(1,-1)$, the only singular zeros. At these nodes the tangent directions are $(h,k)$ with $k=\pm h$.

The full local zero set fails to be a graph $y=y(x)$ exactly at

$$
(0,0),\ (1,-1),\ (3/2,0),\ (-1/2,-1),
$$

and fails to be a graph $x=x(y)$ exactly at

$$
(0,0),\ (1,-1),\ (0,-3/2),\ (1,1/2).
$$

Here a graph means a continuous local graph containing all nearby zeros, not a selected branch.

**Proof.** Differentiation gives $f_x=6x(x-1)$ and $f_y=6y(y+1)$, and the full differential is $f_xh+f_yk$. This gives the four stationary points. The exact increment at $(1,0)$ is

$$
f(x,y)-f(1,0)=(x-1)^2(2x+1)+y^2(2y+3).
$$

Both coefficients are positive near $(1,0)$, and at least one square is positive at every distinct point. The identity $f(1-x,-1-y)=-f(x,y)$ gives the strict maximum at $(0,-1)$. Near zero the two coordinate axes give values of opposite sign. The same reflection gives a saddle at $(1,-1)$. Every local extremum must have zero coordinate derivatives, so this list is exhaustive.

Factorization gives

$$
f(x,y)=(x+y)(2x^2-2xy+2y^2-3x+3y).
$$

Completing squares in the second factor gives the ellipse equation. Solving its quadratic equation in $y$ gives the stated branches and their closed $x$ interval. Substitution of $y=-x$ gives exactly the two intersections. The expansions at them are

$$
f(th,tk)=3t^2(k^2-h^2)+2t^3(h^3+k^3),
$$

$$
f(1+th,-1+tk)=3t^2(h^2-k^2)+2t^3(h^3+k^3).
$$

Thus both intersections have two distinct leading tangent lines.

For graph existence, the implicit function theorem applies wherever the appropriate partial is nonzero. On $S$, solving $f_y=0$ gives exactly the four listed obstructions for $y=y(x)$; solving $f_x=0$ gives the four for $x=x(y)$. Nonzero partials alone do not prove the converse failure. At a node, a continuous ellipse arc and the crossing line give distinct zeros with equal independent coordinate arbitrarily near the node. At $(3/2,0)$, write the two nearby $y$ values as $s(t)\pm t$, where $s(t)=(\sqrt{1-4t^2/3}-1)/2$. Then $6s(t)^2+6s(t)+2t^2=0$, which makes their $y$ contributions equal. A local implicit curve supplies their common $x$ coordinate, giving distinct zeros in the same vertical fiber. Reflection gives the other vertical fold. The symmetry $f(-y,-x)=-f(x,y)$ gives both horizontal folds. These collisions in every neighborhood rule out the full local graph at each listed point.

**Lean declarations:** `Rudin.Chapter09.exercise21_partials`, `Rudin.Chapter09.exercise21_differential`, `Rudin.Chapter09.exercise21_frechet_stationary`, `Rudin.Chapter09.exercise21_extrema`, `Rudin.Chapter09.exercise21_minimum`, `Rudin.Chapter09.exercise21_maximum`, `Rudin.Chapter09.exercise21_stationary_saddles`, `Rudin.Chapter09.exercise21_graph_y`, `Rudin.Chapter09.exercise21_graph_x`, `Rudin.Chapter09.exercise21_zero_set`, `Rudin.Chapter09.exercise21_all_branches`, `Rudin.Chapter09.exercise21_intersections`, `Rudin.Chapter09.exercise21_singular`, `Rudin.Chapter09.exercise21_node_expansions`.

<a id="r09e22"></a>
### 9.22 — A nodal cubic with a loop and two unbounded arms

**Lean source:** [Exercise22.lean](../../Math/Rudin/Chapter09/Exercise22.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $f(x,y)=2x^3+6xy^2-3x^2+3y^2$. Its stationary points are $(0,0)$, a saddle, and $(1,0)$, its unique local minimum, which is strict. There are no local maxima. The zero set $S=\{f=0\}$ is exactly

$$
-1/2<x\le3/2,\qquad y=\pm\sqrt{\frac{x^2(3-2x)}{3+6x}}.
$$

These branches meet only at $(0,0)$ and $(3/2,0)$. The origin is the only singular zero, with tangent lines $y=\pm x$. A parametrization of the entire curve is

$$
P(t)=\left(\frac{3(1-t^2)}{2+6t^2},\frac{3t(1-t^2)}{2+6t^2}\right),\qquad t\in\mathbb R.
$$

The interval $|t|\le1$ gives the loop with $x\ge0$. The remaining parameters give two unbounded arms, both asymptotic to $x=-1/2$: as $t\to+\infty$, $y\to-\infty$, and as $t\to-\infty$, $y\to+\infty$.

On the full zero set, $y=y(x)$ fails locally exactly at $(0,0)$ and $(3/2,0)$. The representation $x=x(y)$ fails exactly at the origin and at

$$
x=\sqrt3/2,\qquad y=\pm\sqrt{\sqrt3/2-3/4}.
$$

**Proof.** The partial derivatives and full differential are

$$
f_x=6(x^2+y^2-x),\qquad f_y=6y(2x+1),\qquad df(h,k)=f_xh+f_yk.
$$

Solving both equations forces $y=0$ and $x=0$ or $1$; the alternative $x=-1/2$ is incompatible with $x^2+y^2-x=0$. The coordinate axes give both signs near zero. At $(1,0)$,

$$
f(x,y)-f(1,0)=(x-1)^2(2x+1)+y^2(6x+3),
$$

which is strictly positive nearby except at the base point. Stationarity is necessary for any local extremum, so there are no others.

The equation $f=0$ rearranges to $(3+6x)y^2=x^2(3-2x)$. Positivity and signs imply $-1/2<x\le3/2$, and division then gives the two branches, including both meeting points. Substitution verifies $f(P(t))=0$. Conversely, a zero with $x\ne0$ is $P(y/x)$; a zero with $x=0$ is the origin, obtained at $t=1$ and $t=-1$. The exact identity

$$
P_1(t)+1/2=\frac2{1+3t^2}
$$

proves the asymptotic $x$ behavior. Since $P_2(t)=tP_1(t)$, it also gives the two limits of $y$. The sign of $1-t^2$ gives the loop parameter interval. At the node,

$$
f(th,tk)=3t^2(k^2-h^2)+2t^3h(h^2+3k^2),
$$

whose quadratic zero directions are precisely $k=\pm h$.

Away from zeros of the relevant partial, the implicit function theorem gives the local graph. On $S$, $f_y=0$ gives only the node and the rightmost point. Reflection in the $x$ axis provides two distinct nearby zeros with the same $x$ at both points. For the other projection, $f_x=0$ on $S$ gives the node or $x>0$, $4x^2=3$, $y^2=x-x^2$, yielding the stated two folds. To prove actual failure, not just failure of an implicit-function hypothesis, divide the cubic in $x$ by a known root. The other roots are

$$
z=\frac{3-2x\pm\sqrt{9+12x-12x^2-48y^2}}4.
$$

Near the node, a parametrized zero and the minus choice give distinct roots in the same horizontal fiber that converge to the node. At either fold, an implicit zero curve and the plus choice do the same. The discriminant is positive nearby; equality of the two roots would force $f_x=0$, which the punctured curves exclude. Thus all listed points, and only those points, fail the full local graph condition.

**Lean declarations:** `Rudin.Chapter09.exercise22_partials`, `Rudin.Chapter09.exercise22_differential`, `Rudin.Chapter09.exercise22_frechet_stationary`, `Rudin.Chapter09.exercise22_extrema`, `Rudin.Chapter09.exercise22_minimum`, `Rudin.Chapter09.exercise22_stationary_saddles`, `Rudin.Chapter09.exercise22_graph_y`, `Rudin.Chapter09.exercise22_graph_x_explicit`, `Rudin.Chapter09.exercise22_zero_set`, `Rudin.Chapter09.exercise22_branches`, `Rudin.Chapter09.exercise22_param_surjective`, `Rudin.Chapter09.exercise22_singular`, `Rudin.Chapter09.exercise22_branch_meetings`, `Rudin.Chapter09.exercise22_node_expansion`, `Rudin.Chapter09.exercise22_tangent_cone`, `Rudin.Chapter09.exercise22_loop_parameters`, `Rudin.Chapter09.exercise22_asymptotes`.

<a id="r09e23"></a>
### 9.23 — Derivatives of an implicitly defined function

**Lean source:** [Exercise23.lean](../../Math/Rudin/Chapter09/Exercise23.lean).

**Inventory status:** Verified as stated.

**Statement.** For $f(x,y_1,y_2)=x^2y_1+e^x+y_2$, there is an open neighborhood $W$ of $(1,-1)$ and a $C^1$ function $g:W\to\mathbb R$ such that

$$
g(1,-1)=0,\qquad g(y_1,y_2)^2y_1+e^{g(y_1,y_2)}+y_2=0.
$$

This graph is unique inside a suitable open neighborhood of $(0,1,-1)$. At the base point, $D_1g=0$ and $D_2g=-1$.

**Proof.** The function is $C^1$, $f(0,1,-1)=0$, and its differential there is $(h,k_1,k_2)\mapsto h+k_2$. In particular the $x$ partial exists and equals $1\ne0$. Apply the scalar implicit-graph construction, grouping $(y_1,y_2)$ as a Banach-space variable. Its derivative formula gives $g'(1,-1)(k_1,k_2)=-k_2$. Restriction to each coordinate line gives the asserted partial derivatives as actual one-variable derivatives. The inverse-function construction supplies the open domain, $C^1$ regularity, equation, base value, and local uniqueness for this same function $g$.

**Lean declarations:** `Rudin.Chapter09.exercise23_zero_value`, `Rudin.Chapter09.exercise23_differential`, `Rudin.Chapter09.exercise23_nonzero_partial`, `Rudin.Chapter09.exercise23_implicit_function`, `Rudin.Chapter09.exercise23_graph_differential`, `Rudin.Chapter09.exercise23_first_partial`, `Rudin.Chapter09.exercise23_second_partial`.

<a id="r09e24"></a>
### 9.24 — A rank-one map onto an ellipse

**Lean source:** [Exercise24.lean](../../Math/Rudin/Chapter09/Exercise24.lean).

**Inventory status:** Verified as stated.

**Statement.** On the punctured Euclidean plane let

$$
F(x,y)=\left(\frac{x^2-y^2}{x^2+y^2},\frac{xy}{x^2+y^2}\right).
$$

Its derivative has rank $1$ at every point of its domain. Its exact range is the ellipse $u^2+4v^2=1$; the second numerator is $xy$, not $2xy$.

**Proof.** Put $d=x^2+y^2>0$. The quotient rule factors the actual derivative as

$$
F'(x,y)(h,k)=(yh-xk)\left(\frac{4xy}{d^2},\frac{y^2-x^2}{d^2}\right).
$$

The linear functional is nonzero because $(x,y)\ne0$. The vector is nonzero as well: if $xy=0$ and $y^2=x^2$, then both coordinates vanish. The range of this derivative is therefore exactly the one-dimensional span of that vector, proving the rank statement even on either coordinate axis.

Direct expansion gives $F_1^2+4F_2^2=1$. Conversely, take $(u,v)$ on the ellipse. If $u=-1$, the equation gives $v=0$, and $F(0,1)=(-1,0)$. Otherwise use the nonzero preimage $(1+u,2v)$. The ellipse equation gives $(1+u)^2+(2v)^2=2(1+u)$, and substitution into $F$ gives $(u,v)$. This includes all boundary points of the ellipse and proves equality of ranges.

**Lean declarations:** `Rudin.Chapter09.exercise24_hasFDerivAt`, `Rudin.Chapter09.exercise24_rank`, `Rudin.Chapter09.exercise24_on_ellipse`, `Rudin.Chapter09.exercise24_range`.

<a id="r09e25"></a>
### 9.25 — A projection from a right inverse on the range

**Lean source:** [Exercise25.lean](../../Math/Rudin/Chapter09/Exercise25.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $A:E\to F$ be real linear. There is a linear map $S:\operatorname{range}A\to E$ with $AS=\operatorname{id}$ on the range. For any such $S$, the map $P=SA:E\to E$ satisfies

$$
P^2=P,\qquad \ker P=\ker A,\qquad \operatorname{range}P=\operatorname{range}S.
$$

If $E$ is finite-dimensional, then $\dim\ker A+\dim\operatorname{range}A=\dim E$. In particular, for $A:\mathbb R^n\to\mathbb R^m$ of rank $r$, $\dim\ker A+r=n$, including rank zero and dimension zero.

**Proof.** The surjective linear map $A:E\to\operatorname{range}A$ has a linear right inverse, obtained by choosing preimages of a basis. Its right-inverse identity gives $P^2=S(AS)A=SA$. If $Px=0$, applying $A$ gives $Ax=0$; the converse follows from linearity of $S$. Every $Px$ lies in the range of $S$, and every $Sz$ is $SAx$ for a preimage $x$ of $z$, proving the range identity.

An idempotent splits $E$ into the complementary subspaces $\ker P$ and $\operatorname{range}P$: $x=(x-Px)+Px$, and their intersection is zero. Also $S$ is injective because $AS$ is the identity. Thus $\dim\operatorname{range}S=\dim\operatorname{range}A$, and taking dimensions in this splitting proves the formula. No division by $r$ occurs. For $A=0$, $S$ is the unique map from the zero range and $P=0$, so the same argument applies.

**Lean declarations:** `Rudin.Chapter09.exercise25_right_inverse`, `Rudin.Chapter09.exercise25_projection`, `Rudin.Chapter09.exercise25_kernel`, `Rudin.Chapter09.exercise25_range`, `Rudin.Chapter09.exercise25_dimension`, `Rudin.Chapter09.exercise25_b`.

<a id="r09e26"></a>
### 9.26 — A continuous mixed partial without a first partial

**Lean source:** [Exercise26.lean](../../Math/Rudin/Chapter09/Exercise26.lean).

**Inventory status:** Verified as stated.

**Statement.** For any nowhere differentiable $g:\mathbb R\to\mathbb R$, let $f(x,y)=g(x)$. Then $D_2f=0$ everywhere, and $D_{12}f=D_1(D_2f)=0$ is continuous everywhere, although $D_1f$ exists nowhere. The source also supplies a concrete such $g$: it is $1$ on rational numbers and $0$ on irrational numbers. Continuity of $f$ is not asserted or required.

**Proof.** For fixed $x$, the function of $y$ is constant, so its derivative genuinely exists and equals zero. For fixed $y$, this proved inner derivative is the zero function of $x$, so its derivative also exists and equals zero. Hence the mixed partial is a continuous constant function. In contrast, the $x$ slice is exactly $g$, and is nowhere differentiable by hypothesis.

For the concrete example, every interval contains both a rational and an irrational number. If $g$ were continuous at any $x$, a sufficiently small neighborhood would force $|g(t)-g(x)|<1/2$. Choosing $t$ of the opposite rationality gives difference $1$, a contradiction. Thus $g$ is nowhere continuous and therefore nowhere differentiable. This verifies that the construction has an actual example, rather than only a conditional hypothesis.

**Lean declarations:** `Rudin.Chapter09.exercise26_second_partial`, `Rudin.Chapter09.exercise26_mixed_partial`, `Rudin.Chapter09.exercise26_mixed_continuous`, `Rudin.Chapter09.exercise26_first_nowhere`, `Rudin.Chapter09.exercise26_nowhere_not_continuous`, `Rudin.Chapter09.exercise26_nowhere_not_differentiable`, `Rudin.Chapter09.exercise26_example`.

<a id="r09e27"></a>
### 9.27 — Continuous first partials and unequal mixed partials

**Lean source:** [Exercise27.lean](../../Math/Rudin/Chapter09/Exercise27.lean).

**Inventory status:** Verified as stated.

**Statement.** Set $f(0,0)=0$ and, elsewhere,

$$
f(x,y)=\frac{xy(x^2-y^2)}{x^2+y^2}.
$$

The function is $C^1$ on the entire plane. Both mixed partials exist everywhere and are continuous off the origin, but both are discontinuous there. With the rightmost derivative taken first,

$$
D_{12}f(0,0)=1,\qquad D_{21}f(0,0)=-1.
$$

**Proof.** The first partials have $P(0,0)=Q(0,0)=0$ and, off the origin, are

$$
P(x,y)=\frac{y(x^4+4x^2y^2-y^4)}{(x^2+y^2)^2},\qquad Q(x,y)=-P(y,x).
$$

For the first partial, the slice $y=0$ is constant zero; for $y\ne0$, the quotient rule gives $P$. Antisymmetry $f(x,y)=-f(y,x)$ gives the second partial. The estimates

$$
|f(x,y)|\le |x||y|,\qquad |P(x,y)|\le3|y|,\qquad |Q(x,y)|\le3|x|
$$

prove continuity of all three at zero. Away from zero they are rational functions with nonzero denominator. Continuous first partials then give the actual continuous total derivative, hence $C^1$ regularity.

For $(x,y)\ne(0,0)$ put

$$
K(x,y)=\frac{x^6+9x^4y^2-9x^2y^4-y^6}{(x^2+y^2)^3}.
$$

For $(x,y)\ne(0,0)$, direct differentiation gives $D_{21}f=K(x,y)$ and $D_{12}f=-K(y,x)$. On the vertical axis, the identity $P(0,y)=-y$ proves the derivative of $P$ directly, including $D_{21}f(0,0)=-1$; the swapped identity gives $D_{12}f(0,0)=1$. Thus these are derivatives of the actual first partials, not values assigned to nonexistent derivatives.

The formulas with $K$ prove continuity away from zero. For nonzero $x$, $D_{21}f(x,0)=1$, contrary to its value $-1$ at zero. For nonzero $y$, $D_{12}f(0,y)=-1$, contrary to its value $1$ at zero. Restricting any alleged continuity to these axes gives contradictions.

**Lean declarations:** `Rudin.Chapter09.exercise27_zero`, `Rudin.Chapter09.exercise27_continuous`, `Rudin.Chapter09.exercise27_first_partials`, `Rudin.Chapter09.exercise27_actual_first_partials`, `Rudin.Chapter09.exercise27_C1`, `Rudin.Chapter09.exercise27_mixed_existence`, `Rudin.Chapter09.exercise27_mixed_continuous_off_zero`, `Rudin.Chapter09.exercise27_mixed_discontinuous`, `Rudin.Chapter09.exercise27_D12_zero`, `Rudin.Chapter09.exercise27_D21_zero`, `Rudin.Chapter09.exercise27_mixed_values`, `Rudin.Chapter09.exercise27_D12_formula`, `Rudin.Chapter09.exercise27_D21_formula`.

<a id="r09e28"></a>
### 9.28 — Failure to interchange differentiation and integration

**Lean source:** [Exercise28.lean](../../Math/Rudin/Chapter09/Exercise28.lean).

**Inventory status:** Verified as stated.

**Statement.** For $t\ge0$, define

$$
\phi(x,t)=\begin{cases}
x,&0\le x\le\sqrt t,\\
-x+2\sqrt t,&\sqrt t\le x\le2\sqrt t,\\
0,&\text{otherwise},
\end{cases}
$$

and for $t<0$ set $\phi(x,t)=-\phi(x,|t|)$. The closed pieces agree at their shared endpoints. This function is jointly continuous on $\mathbb R^2$, and $D_2\phi(x,0)=0$ for every real $x$. Nevertheless, if $I(t)=\int_{-1}^1\phi(x,t)\,dx$, then $I(t)=t$ for $|t|<1/4$, so

$$
I'(0)=1\ne0=\int_{-1}^1D_2\phi(x,0)\,dx.
$$

The integrals are verified both as ordinary interval integrals and as the source's closed-cell Darboux and tagged-refinement integrals.

**Proof.** Write $T(x,r)=\max(0,\min(x,2r-x))$. For $r\ge0$, it equals $x$ on $[0,r]$, $2r-x$ on $[r,2r]$, and zero outside, with matching endpoint values. Also $0\le T(x,r)\le r$. Away from $t=0$, continuity follows from the min/max formula and the locally constant choice of sign. At every point of the whole $t=0$ axis, the bound $|\phi(x,t)|\le\sqrt{|t|}$ proves continuity, since $\phi(x,0)=0$.

For fixed $x\le0$, $\phi(x,t)$ is always zero. For fixed $x>0$, $2\sqrt{|t|}<x$ for all sufficiently small $t$, so the function is again identically zero near $t=0$. Its parameter derivative is therefore an actual derivative equal to zero for every $x$.

Every slice in $x$ is continuous and hence integrable on each finite interval. If $r\ge0$ and $2r\le1$, split $[-1,1]$ at $0,r,2r$. The two nonzero integrals are each $r^2/2$, so the total is $r^2$, including the degenerate case $r=0$. Take $r=\sqrt{|t|}$ and use the sign in the definition: the result is $t$ when $|t|<1/4$. Thus $I$ agrees with the identity near zero and $I'(0)=1$.

For completeness, the source integral is the supremum of lower sums over weakly increasing partitions of $[-1,1]$, using infima on closed cells. The continuous-integrand bridge for the integrator $\alpha(x)=x$ identifies this value with the interval integral, and also proves equality with upper sums and the tagged-refinement criterion. The parameter partial is identically zero, so its Darboux and interval integrals both equal zero. Hence neither side of the failed interchange relies on an undefined derivative or an unproved integrability assumption.

**Lean declarations:** `Rudin.Chapter09.exercise28_piecewise`, `Rudin.Chapter09.exercise28_source_nonnegative`, `Rudin.Chapter09.exercise28_source_negative`, `Rudin.Chapter09.exercise28_continuous`, `Rudin.Chapter09.exercise28_parameter_partial`, `Rudin.Chapter09.exercise28_slice_integrable`, `Rudin.Chapter09.exercise28_darboux_bridge`, `Rudin.Chapter09.exercise28_source_integral`, `Rudin.Chapter09.exercise28_integral_value`, `Rudin.Chapter09.exercise28_failed_interchange`, `Rudin.Chapter09.exercise28_failed_interchange_interval`, `Rudin.Chapter09.exercise28_tent_integral`, `Rudin.Chapter09.exercise28_integral_derivative`, `Rudin.Chapter09.exercise28_partial_integral`.

<a id="r09e29"></a>
### 9.29 — Permutation of coordinate derivatives

**Lean source:** [Exercise29.lean](../../Math/Rudin/Chapter09/Exercise29.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $E\subset\mathbb R^n$ be open and $f\in C^m(E)$. Every ordered coordinate derivative of length $k\le m$ is unchanged by a permutation of its indices, including repeated indices. In particular, for $f\in C^k(E)$,

$$
D_{i_{\sigma(1)}}\cdots D_{i_{\sigma(k)}}f(a)=D_{i_1}\cdots D_{i_k}f(a),\qquad a\in E.
$$

The empty list gives $f$ itself. All intermediate derivatives used here genuinely exist: a derivative of length $j$ is $C^r$ whenever $j+r\le m$.

**Proof.** Define a coordinate derivative by applying the Fréchet derivative to the corresponding Euclidean coordinate vector, and iterate from the right. Induction on the list length proves the remaining regularity statement by differentiating a $C^{r+1}$ function and evaluating on a fixed vector. If the length is less than $m$, this gives an existing Fréchet derivative. Composition with $t\mapsto a+te_i$ proves that the next coordinate derivative is also the ordinary one-variable partial at $t=0$.

For a $C^2$ function, symmetry of the continuous second Fréchet derivative gives $D_iD_jg=D_jD_ig$. Now use that adjacent swaps generate permutations. A swap of two leading indices is valid because the remaining inner derivative is $C^2$. If a permutation is already valid for an inner list, the resulting functions agree throughout $E$; openness makes them equal near every $a\in E$, so their next derivatives agree there too. Transitivity completes the induction over permutations. This proves equality of actual coordinate derivatives without assuming symmetry of a higher differential as a separate hypothesis.

**Lean declarations:** `Rudin.Chapter09.mixedPartial_contDiffOn`, `Rudin.Chapter09.mixedPartial_hasFDerivAt`, `Rudin.Chapter09.mixedPartial_hasDerivAt`, `Rudin.Chapter09.coordinatePartial_comm`, `Rudin.Chapter09.exercise29_permutation_invariance`, `Rudin.Chapter09.exercise29_ordered_permutation`.

<a id="r09e30"></a>
### 9.30 — Ordered and multi-index Taylor expansions

**Lean source:** [Exercise30.lean](../../Math/Rudin/Chapter09/Exercise30.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $E\subset\mathbb R^n$ be open, $m\ge1$, $f\in C^m(E)$, and $a\in E$. For $h(t)=f(a+tx)$, at every parameter with $a+tx\in E$ and for $0\le k\le m$,

$$
h^{(k)}(t)=\sum_{i_1,\ldots,i_k=1}^n(D_{i_1}\cdots D_{i_k}f)(a+tx)x_{i_1}\cdots x_{i_k}.
$$

The $k=0$ expression is $f(a+tx)$. If the entire segment $a+tx$, $0\le t\le1$, lies in $E$, then

$$
f(a+x)=\sum_{k=0}^{m-1}\frac1{k!}\sum_{i_1,\ldots,i_k=1}^n(D_{i_1}\cdots D_{i_k}f)(a)x_{i_1}\cdots x_{i_k}+r(x).
$$

The actual remainder has both forms

$$
r(x)=\frac1{(m-1)!}\int_0^1(1-t)^{m-1}D^mf(a+tx)[x,\ldots,x]\,dt
=\frac1{m!}D^mf(a+\theta x)[x,\ldots,x]
$$

for some $0<\theta<1$. Locally $r(x)=O(|x|^m)$, and hence

$$
\frac{r(x)}{|x|^{m-1}}\longrightarrow0\qquad(x\to0,\ x\ne0).
$$

The same polynomial, with the same remainder, is

$$
\sum_{s_1+\cdots+s_n\le m-1}\frac{(D_1^{s_1}\cdots D_n^{s_n}f)(a)}{s_1!\cdots s_n!}x_1^{s_1}\cdots x_n^{s_n},
$$

where all $s_i$ are nonnegative integers. These results include $m=1$ and dimension zero, with the usual empty-sum and empty-product conventions.

**Proof.** First identify each ordered coordinate derivative with $D^kf$ evaluated on its coordinate vectors. Induction uses the existing derivative of $D^{k-1}f$ and local equality on the open domain. Expand each copy of $x=\sum_i x_ie_i$ by multilinearity. The resulting diagonal evaluation is exactly the ordered coordinate sum.

The chain rule gives a genuine derivative jet along the line: the derivative of $D^kf(a+tx)[x,\ldots,x]$ is $D^{k+1}f(a+tx)[x,\ldots,x]$ for $k<m$. The inverse image of $E$ under the line map is open, so local equality and induction identify this jet with the iterated scalar derivatives of $h$. This proves the formula wherever the line is in $E$, not just inside the specified segment.

Apply one-variable Taylor theory on $[0,1]$ to obtain the integral and Lagrange remainders. The integral remainder integrand is continuous on the whole segment, hence integrable. Continuity of $D^mf$ near $a$ gives a ball on which its operator norm is bounded by a constant $C$. For sufficiently small $x$, the full segment is in this ball. Multilinearity gives $|D^mf(a+tx)[x,\ldots,x]|\le C|x|^m$; also $0\le(1-t)^{m-1}\le1$. The integral formula therefore bounds $|r(x)|$ by a fixed constant times $|x|^m$. Since $|x|^m=o(|x|^{m-1})$, the required little-o estimate and punctured limit follow. When $m=1$, this is $r(x)\to0$; in dimension zero the punctured limit has no nonzero points.

Finally group the ordered $k$-tuples by their coordinate multiplicities $s=(s_1,\ldots,s_n)$. The exact number with these multiplicities is $k!/(s_1!\cdots s_n!)$. The source proves this count by comparing the coefficient of the corresponding monomial in the ordered and multinomial expansions of $(X_1+\cdots+X_n)^k$. Exercise 29 makes the derivative identical for all tuples in a group, and their products all equal $x_1^{s_1}\cdots x_n^{s_n}$. Cancel the factor $k!$ against the Taylor coefficient. Taking the union of the groups for $0\le k<m$ gives exactly total degree at most $m-1$, including the constant term, and proves equality of the two polynomials.

**Lean declarations:** `Rudin.Chapter09.mixedPartial_eq_iteratedFDeriv`, `Rudin.Chapter09.orderedCoordinateSum_eq`, `Rudin.Chapter09.exercise30_sourceJet`, `Rudin.Chapter09.line_iteratedDeriv`, `Rudin.Chapter09.exercise30_a`, `Rudin.Chapter09.exercise30_b_expansion`, `Rudin.Chapter09.exercise30_b_lagrange`, `Rudin.Chapter09.orderedCoordinateSum_zero`, `Rudin.Chapter09.taylorRemainder_intervalIntegrable`, `Rudin.Chapter09.taylorRemainder_isBigO`, `Rudin.Chapter09.exercise30_b_remainder_isLittleO`, `Rudin.Chapter09.exercise30_b_remainder`, `Rudin.Chapter09.Exercise30Combinatorics.card_counts_fiber`, `Rudin.Chapter09.Exercise30Combinatorics.sum_list_perm_invariant`, `Rudin.Chapter09.mem_taylorMultiIndices_iff`, `Rudin.Chapter09.exercise30_c`, `Rudin.Chapter09.exercise30_multiIndex_expansion`.

<a id="r09e31"></a>
### 9.31 — Corrected second-derivative tests and a singular obstruction

**Lean source:** [Exercise31.lean](../../Math/Rudin/Chapter09/Exercise31.lean).

**Inventory status:** Verified refutation and correction.

**Statement.** The printed claim is false: $C^3$ regularity near a stationary point and at least one nonzero second partial do not ensure that the quadratic Taylor polynomial determines the type of local extremum. The smooth planar functions

$$
f_+(x,y)=x^2+y^4,\qquad f_-(x,y)=x^2-y^4
$$

have the same value, zero gradient, nonzero singular Hessian $\operatorname{diag}(2,0)$, and quadratic Taylor polynomial $x^2$ at zero. The first has a strict global minimum there; the second has neither a local minimum nor a local maximum. The obstruction extends to every dimension at least two, and negation gives the corresponding negative-semidefinite obstruction.

The valid tests are as follows. Suppose $f$ is $C^3$ near $a$ in a finite-dimensional real normed space and $f'(a)=0$, and let $B=f''(a)$ be its actual Hessian. If $B(v,v)>0$ for every $v\ne0$, then $a$ is a strict local minimum. If $B(v,v)<0$ for every $v\ne0$, it is a strict local maximum. If $B$ has both a positive and a negative quadratic direction, it is neither a local minimum nor a local maximum. A nonzero positive-semidefinite Hessian excludes a local maximum but does not decide whether a local minimum exists; reverse the signs for a negative-semidefinite Hessian. In dimension one a nonzero Hessian is decisive by its sign. In dimension zero the nonzero-Hessian hypothesis is impossible.

**Proof.** The source first derives the genuine quadratic expansion

$$
f(a+h)-f(a)=\tfrac12B(h,h)+o(|h|^2).
$$

Local $C^3$ regularity supplies first derivatives in a neighborhood and differentiability of the derivative at $a$. Symmetry of this second derivative makes the derivative of $B(x-a,x-a)/2$ equal to $B(x-a,\cdot)$. Subtract this quadratic function and $f(a)$ from $f$. The resulting derivative is $o(|x-a|)$. The mean-value estimate on a small convex ball then gives an error $o(|x-a|^2)$, proving the expansion rather than assuming it.

For positive definite $B$, continuity and compactness of the unit sphere give $c>0$ with $B(h,h)\ge c|h|^2$. Choose the error smaller than $(c/4)|h|^2$. The increment is then positive for every sufficiently small nonzero $h$, giving a strict minimum on a full punctured neighborhood. Negation proves the negative definite test. A positive direction $v$ gives $f(a+tv)>f(a)$ for sufficiently small nonzero $t$, so it excludes a local maximum; a negative direction excludes a local minimum. Both directions give the indefinite conclusion. These directional exclusions do not require finite dimension.

For the semidefinite conclusion, a symmetric nonzero positive-semidefinite form has a positive direction. Otherwise all diagonal values vanish, and expansion of $B(v+w,v+w)$ with symmetry forces every $B(v,w)$ to vanish, a contradiction. Apply the directional exclusion, and negate for the negative case. In one dimension $B(x,y)=xyB(1,1)$, so $B\ne0$ implies $B(1,1)\ne0$ and one of the definite tests applies. On a zero-dimensional space every bilinear form is zero.

To show exactly why the singular cases remain inconclusive, in dimension $d\ge2$ define

$$
F_c(p)=\sum_{j\ne2}p_j^2+c\,p_2^4.
$$

For every $c$, these polynomial functions have value and first derivative zero at the origin and the same Hessian

$$
B(v,w)=2\sum_{j\ne2}v_jw_j.
$$

This Hessian is nonnegative, is nonzero on the first coordinate vector, and has the nonzero second coordinate vector in its kernel. The actual quadratic Taylor polynomial is $\sum_{j\ne2}h_j^2$, independent of $c$. For $c=1$, every nonzero point has positive value, giving a strict global and local minimum. For $c=-1$, the first axis has values $t^2>0$ and the second has values $-t^4<0$ arbitrarily close to zero, giving neither extremum. Their negatives have the same negative-semidefinite quadratic polynomial; one has a strict local maximum and the other has neither extremum. For $d=2$ these are exactly the displayed planar examples. Thus the source's original classification is refuted, while all stated corrected tests retain their full hypotheses and singular cases.

**Lean declarations:** `Rudin.Chapter09.exercise31_counterexample`, `Rudin.Chapter09.exercise31_planar_formula`, `Rudin.Chapter09.exercise31_counter_hessian_axis`, `Rudin.Chapter09.exercise31_zero_dimension`, `Rudin.Chapter09.exercise31_one_dimension`, `Rudin.Chapter09.exercise31_counter_hessian_nonnegative`, `Rudin.Chapter09.exercise31_counter_hessian_nonzero`, `Rudin.Chapter09.exercise31_counter_hessian_kernel`, `Rudin.Chapter09.exercise31_counter_same_jet`, `Rudin.Chapter09.exercise31_counter_taylor`, `Rudin.Chapter09.exercise31_counter_negative_jet`, `Rudin.Chapter09.exercise31_counter_negative_taylor`, `Rudin.Chapter09.exercise31_counter_negative_behavior`, `Rudin.Chapter09.exercise31_quadratic_expansion`, `Rudin.Chapter09.exercise31_positive_test`, `Rudin.Chapter09.exercise31_negative_test`, `Rudin.Chapter09.exercise31_indefinite_test`, `Rudin.Chapter09.exercise31_semidefinite_exclusions`, `Rudin.Chapter09.exercise31_counter_minimum`, `Rudin.Chapter09.exercise31_counter_neither`.

<a id="chapter-10"></a>

## Chapter 10 — Integration of Differential Forms

**Exercises:** [1](#r10e01) · [2](#r10e02) · [3](#r10e03) · [4](#r10e04) · [5](#r10e05) · [6](#r10e06) · [7](#r10e07) · [8](#r10e08) · [9](#r10e09) · [10](#r10e10) · [11](#r10e11) · [12](#r10e12) · [13](#r10e13) · [14](#r10e14) · [15](#r10e15) · [16](#r10e16) · [17](#r10e17) · [18](#r10e18) · [19](#r10e19) · [20](#r10e20) · [21](#r10e21) · [23](#r10e23) · [28](#r10e28) · [29](#r10e29) · [30](#r10e30) · [32](#r10e32)

<a id="r10e01"></a>
### 10.1 — Integration order for a convex zero extension

**Lean source:** [Exercise01.lean](../../Math/Rudin/Chapter10/Exercise01.lean).

**Inventory status:** Pending verification.

**Statement.** Let $H\subset\mathbb R^n$ be compact and convex, and let $f:H\to\mathbb R$ or $\mathbb C$ be continuous. Retain the values of $f$ on the boundary and extend it by zero outside $H$. There is an enclosing coordinate cell on which every repeated integral exists, at every remaining parameter, in every coordinate order. Each order has value $\int_H f$. Order independence also holds on any coordinate cell with ordered bounds, whether or not it contains $H$.

The results do not require nonempty interior. They include empty sets, lower-dimensional sets, dimension zero, and cells with degenerate sides. In dimension zero, integration is evaluation.

**Proof.** The zero extension is bounded and measurable. For every finite-dimensional affine parameter map $L$, the inverse image $L^{-1}(H)$ is closed and convex. Its frontier has measure zero in the parameter space. Away from that frontier, the composite zero extension is continuous: inside, use the continuity of $f$ on $H$; outside, the composite is locally zero. This argument applies to every affine section, including boundary sections and collapsed sections.

This regularity is preserved by integration in one coordinate. Indeed, apply Fubini to the almost-everywhere continuity statement in the joint parameter and integration variables. For almost every parameter, the integrand is continuous in the parameter at almost every integration point. Its uniform bound then permits dominated convergence. The resulting marginal is bounded, measurable, and almost everywhere continuous on every affine parameter space. Each individual coordinate row is bounded and almost everywhere continuous, so the one-dimensional Darboux criterion supplies its actual Riemann integral. Induction gives all repeated source integrals, not just almost-everywhere row integrals. Fubini, now with integrability established, identifies their values with the cell measure integral.

For the approximation argument, extend $f$ continuously to an ambient function $g$. Choose continuous cutoffs $c_j$ with $0\le c_j\le1$, zero outside $H$ and on its frontier, tending to $1$ in its interior. The source uses distance-based thickened indicators with width $1/(j+1)$. The functions $c_jg$ are continuous, have topological support in $H$, and have a common bound. They converge to the literal zero extension outside the null convex frontier. No uniform convergence at nonzero boundary values is asserted. Dominated convergence transfers this approximation to each repeated value. The continuous-cell theorem gives the same value for all orders at each $j$; uniqueness of limits gives order independence for the zero extension.

For complex values, apply the real argument to the real and imaginary parts. The component equivalence for complex tagged sums supplies actual complex one-dimensional source integrals at each stage. Compactness supplies strictly ordered enclosing bounds, and the volume-preserving Euclidean coordinate map identifies the common enclosing-cell value with $\int_H f$. The plane-coordinate conclusions give the same witnesses in $\mathbb R\times\mathbb R$.

Inventory obligations `R10E01.existence` and `R10E01.order_independence` remain marked in progress; the current source contains the results above.

**Lean declarations:** `Rudin.Chapter10.Exercise01.existence_real`, `Rudin.Chapter10.Exercise01.existence_complex`, `Rudin.Chapter10.Exercise01.plane_source_real`, `Rudin.Chapter10.Exercise01.plane_source_complex`, `Rudin.Chapter10.Exercise01.order_independence_real`, `Rudin.Chapter10.Exercise01.order_independence_complex`, `Rudin.Chapter10.Exercise01.real_existence`, `Rudin.Chapter10.Exercise01.complex_existence`, `Rudin.Chapter10.Exercise01.continuous_approximations`, `Rudin.Chapter10.Exercise01.continuous_approximations_complex`, `Rudin.Chapter10.Exercise01.approximation_source_limit`, `Rudin.Chapter10.Exercise01.real_order_independence`, `Rudin.Chapter10.Exercise01.complex_order_independence`.

<a id="r10e02"></a>
### 10.2 — Unequal repeated integrals near a singular point

**Lean source:** [Exercise02.lean](../../Math/Rudin/Chapter10/Exercise02.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $\phi_i:\mathbb R\to\mathbb C$ be continuous, supported in $(2^{-i},2^{1-i})$, with $\int_{\mathbb R}\phi_i=1$, for $i\ge1$. Real functions are included; positivity is not assumed. Set

$$
f(x,y)=\sum_{i\ge1}\bigl(\phi_i(x)-\phi_{i+1}(x)\bigr)\phi_i(y).
$$

The series is pointwise finite, its ordered partial sums converge to $f$, and it is locally finite away from $(0,0)$. The function has compact support in $[0,1]^2$ and is continuous away from the origin. Every coordinate section is continuous and compactly supported, and both integrations in each order exist, including their source Riemann integrals. Their values are

$$
\int_{\mathbb R}\left(\int_{\mathbb R}f(x,y)\,dx\right)dy=0,
\qquad
\int_{\mathbb R}\left(\int_{\mathbb R}f(x,y)\,dy\right)dx=1.
$$

Moreover, $f(0,0)=0$, but $f$ is unbounded in every neighborhood of the origin, is discontinuous there, and is not integrable on the plane. The geometric conclusions also hold in Euclidean plane coordinates.

**Proof.** Write $r_n=2^{-n}$, with source index $i=n+1$. At any fixed nonzero coordinate, sufficiently small dyadic intervals miss that coordinate and a whole neighborhood of it. At coordinate zero, every $\phi_i$ vanishes. Thus every point kills a tail of the series. Away from the origin, at least one coordinate kills the tail on a neighborhood. The remaining terms form a finite sum of continuous functions. All terms vanish outside $[0,1]^2$, so the closure of the nonzero set is compact.

For fixed $y$, only finitely many terms remain as functions of $x$. Integrating each gives $(1-1)\phi_i(y)=0$. For fixed $x$, choose a finite cutoff with vanishing tail. Integration in $y$ gives the telescoping sum

$$
\sum_{i=1}^{N}\bigl(\phi_i(x)-\phi_{i+1}(x)\bigr)=\phi_1(x).
$$

The outer integrals are therefore the integrals of zero and $\phi_1$, respectively. Each section is continuous and supported in $[0,1]$. The continuous-function bridge supplies Darboux integrals for its real and imaginary parts and complex tagged-sum convergence. The real case also has explicit witnesses in the recursive two-coordinate source predicate for both orders.

Distinct dyadic support intervals do not overlap. If $\phi_i(x)\ne0$, then all other $\phi_j(x)$ vanish, and

$$
f(x,x)=\phi_i(x)^2,\qquad |f(x,x)|=|\phi_i(x)|^2.
$$

Integral one on an interval contained in $[0,2^{1-i}]$ rules out a uniform bound $M$ whenever $M2^{1-i}<1$: otherwise the norm of that integral would be less than one. Choose $i$ so large that this interval is inside a prescribed diagonal neighborhood and the resulting squared value exceeds any prescribed bound. This proves local unboundedness without positivity, even for complex functions. It also proves discontinuity at the origin. Finally, plane integrability would permit Fubini and force the two repeated values to agree, contradicting $0\ne1$. Complexification preserves the actual real series and transfers all the real conclusions.

**Lean declarations:** `Rudin.Chapter10.Exercise02.Family.well_defined`, `Rudin.Chapter10.Exercise02.Family.ordered_convergence`, `Rudin.Chapter10.Exercise02.Family.locally_finite_off_origin`, `Rudin.Chapter10.Exercise02.Family.compact_support`, `Rudin.Chapter10.Exercise02.Family.continuous_off_origin`, `Rudin.Chapter10.Exercise02.Family.x_then_y`, `Rudin.Chapter10.Exercise02.Family.y_then_x`, `Rudin.Chapter10.Exercise02.Family.unbounded_every_neighborhood`, `Rudin.Chapter10.Exercise02.Family.discontinuous_origin`, `Rudin.Chapter10.Exercise02.Family.not_integrable`, `Rudin.Chapter10.Exercise02.Family.euclidean_conclusions`, `Rudin.Chapter10.Exercise02.RealFamily.complex_f`, `Rudin.Chapter10.Exercise02.RealFamily.real_case`, `Rudin.Chapter10.Exercise02.RealFamily.source_orders`.

<a id="r10e03"></a>
### 10.3 — Local factorization into primitive maps

**Lean source:** [Exercise03.lean](../../Math/Rudin/Chapter10/Exercise03.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $E\subset\mathbb R^n$ be open and contain zero. Suppose $F$ is $C^1$ on $E$, $F(0)=0$, and $A=F'(0)$ is invertible. Then $F_1=A^{-1}F$ has derivative $I$ at zero. On a neighborhood of zero it is a composition of exactly $n$ primitive $C^1$ maps:

$$
F_1=G_n\circ\cdots\circ G_1,\qquad
F=A\circ G_n\circ\cdots\circ G_1.
$$

Each factor fixes zero, has derivative $I$ there, and has an open primitive domain containing zero. A primitive map changes at most one coordinate. For $n=0$, the factor family is empty and the composition is the identity.

The planar flip $(x,y)\mapsto(y,x)$ cannot be a composition $H\circ G$ of two primitive maps on any neighborhood $U$ of zero, provided $G(U)$ lies in the primitive domain of $H$. This obstruction requires no regularity of $G$ or $H$.

**Proof.** The chain rule gives $(A^{-1}F)'(0)=A^{-1}A=I$. For the normalized map, let $P_m$ replace the first $m$ input coordinates by their values under $F_1$, leaving the others unchanged. Every $P_m$ fixes zero and has derivative $I$ there. The inverse function theorem supplies a $C^1$ local inverse $H_m$ with derivative $I$ at zero and both inverse identities on neighborhoods.

Define the next factor by replacing only coordinate $m+1$ of $z$ by the corresponding coordinate of $F_1(H_m(z))$. All other coordinates remain unchanged. Near zero, this factor sends $P_m(x)$ to $P_{m+1}(x)$. The chain rule gives derivative $I$ for the factor. Its $C^1$ germ can be restricted to an open neighborhood. Induction identifies the first $m$ factors with $P_m$ near zero. Since $P_0=I$ and $P_n=F_1$, exactly $n$ factors suffice. Multiplying by $A$ recovers $F$.

For the flip, consider which coordinate each primitive factor can change. If both change the same coordinate, the other coordinate remains fixed, contrary to a flip at a small point on the other axis. If $G$ changes the first coordinate and $H$ the second, the first output coordinate forces $G(x,y)=(y,y)$ on $U$. Thus $G(a,0)=G(0,0)$ for a sufficiently small nonzero $a$, while their flipped images are distinct. The composition cannot have both values. The case where $G$ changes the second coordinate and $H$ the first is the same argument using $(0,a)$.

**Lean declarations:** `Rudin.Chapter10.exercise03_normalization`, `Rudin.Chapter10.exercise03_partial_inverse`, `Rudin.Chapter10.exercise03_factorization`, `Rudin.Chapter10.exercise03_a`, `Rudin.Chapter10.exercise03_a_finite`, `Rudin.Chapter10.exercise03_b`.

<a id="r10e04"></a>
### 10.4 — Two explicit primitive factorizations

**Lean source:** [Exercise04.lean](../../Math/Rudin/Chapter10/Exercise04.lean).

**Inventory status:** Verified as stated.

**Statement.** Define

$$
\begin{aligned}
F(x,y)&=(e^x\cos y-1,e^x\sin y),\\
G_1(x,y)&=(e^x\cos y-1,y),&G_2(u,v)&=(u,(1+u)\tan v),\\
H_2(x,y)&=(x,e^x\sin y),&H_1(u,v)&=(\sqrt{e^{2u}-v^2}-1,v).
\end{aligned}
$$

On $U=\{(x,y):-\pi/2<y<\pi/2\}$, one has $F=G_2\circ G_1=H_1\circ H_2$. Here $G_1(U)\subset U$ and $H_2(U)\subset V=\{(u,v):e^{2u}-v^2>0\}$. Both $U$ and $V$ are open neighborhoods of zero. The four factors are primitive on these domains. The maps $F,G_1,H_2$ are globally smooth; $G_2$ is smooth on $U$, and $H_1$ is smooth on $V$. The derivatives of $F,G_1,G_2$ at zero are $I$, so all three Jacobians there are $1$.

**Proof.** On $U$, $\cos y>0$. The first factor leaves $y$ unchanged, and

$$
(1+(e^x\cos y-1))\tan y=e^x\sin y.
$$

This proves the first factorization and its domain condition. For the second, use

$$
e^{2x}-(e^x\sin y)^2=(e^x\cos y)^2.
$$

The right side is positive on $U$. Thus $H_2$ lands in $V$, and its positive square root is $e^x\cos y$, not its negative. This gives the stated formula for $H_1\circ H_2$. Each primitive assertion follows from the unchanged coordinate. Standard composition rules give smoothness, using the nonzero cosine and positive square-root arguments on the specified domains. Differentiating the displayed coordinates at zero gives the two coordinate projections as rows for each of $F,G_1,G_2$. Their derivative matrices are therefore $I$, with determinant $1$.

**Lean declarations:** `Rudin.Chapter10.exercise04_domains`, `Rudin.Chapter10.exercise04_primitive_maps`, `Rudin.Chapter10.exercise04_smooth`, `Rudin.Chapter10.exercise04_first_factorization`, `Rudin.Chapter10.exercise04_alternative_factor`, `Rudin.Chapter10.exercise04_derivatives`, `Rudin.Chapter10.exercise04_jacobians`.

<a id="r10e05"></a>
### 10.5 — A finite partition of unity in a metric space

**Lean source:** [Exercise05.lean](../../Math/Rudin/Chapter10/Exercise05.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $K$ be a compact subset of an arbitrary metric space $X$, and let $(U_i)_{i\in I}$ be an open cover of $K$. There are a finite index set $J$, a choice $a:J\to I$, and continuous functions $\psi_j:X\to[0,1]$ such that

$$
\operatorname{supp}\psi_j\subset U_{a(j)},\qquad
\sum_{j\in J}\psi_j(x)=1\quad(x\in K).
$$

Support means the closure of the nonzero set. Neither local compactness of $X$ nor compact support of the functions is required. Empty $K$ is allowed.

**Proof.** For disjoint nonempty closed sets $A,B$, the metric separator

$$
s(x)=\frac{d(x,A)}{d(x,A)+d(x,B)}
$$

is continuous, lies in $[0,1]$, is zero on $A$, and is one on $B$. Its denominator is positive at each point because the sets are closed and disjoint. If $A$ is empty use the constant one; if only $B$ is empty use zero.

Given $x\in U_i$, normality of metric spaces supplies open neighborhoods $V,W$ with $x\in V$, $\overline V\subset W$, and $\overline W\subset U_i$. Separate $W^c$ and $\overline V$. The resulting bump is one on $V$, zero outside $W$, and has support in $\overline W\subset U_i$. Compactness selects finitely many such $V$ covering $K$, with bumps $b_1,\ldots,b_N$. Use the ordered-product construction

$$
\psi_j=b_j\prod_{\ell<j}(1-b_\ell).
$$

Every function is continuous, lies in $[0,1]$, and has support contained in that of its own bump. The identity $\sum_j\psi_j=1-\prod_j(1-b_j)$ gives sum one on $K$, since some bump is one at each point of $K$. The empty compact set permits an empty family. The finite-bump extraction is also proved separately and reused for smooth bumps.

**Lean declarations:** `Rudin.Chapter10.exercise05_separator_spec`, `Rudin.Chapter10.exercise05_bump`, `Rudin.Chapter10.exercise05_finite_bumps`, `Rudin.Chapter10.exercise05_metric_partition`.

<a id="r10e06"></a>
### 10.6 — A smooth finite partition of unity

**Lean source:** [Exercise06.lean](../../Math/Rudin/Chapter10/Exercise06.lean).

**Inventory status:** Pending verification.

**Statement.** For compact $K\subset\mathbb R^n$ and any open cover $(U_i)$ of $K$, the finite subordinate partition in Exercise 10.5 can be chosen globally $C^\infty$. Each function also has compact support, is differentiable, takes values in $[0,1]$, and the functions sum to one on $K$. Empty $K$ and dimension zero are included.

**Proof.** Let $g(s)$ be the flat function from Chapter 8, equal to $e^{-1/s^2}$ for $s\ne0$ and zero at zero. Then $b(t)=g(\sqrt t)$ is $e^{-1/t}$ for $t>0$ and zero for $t\le0$. The source identifies this function exactly with the smooth positive-side flat function. Consequently

$$
\eta(t)=\frac{b(t)}{b(t)+b(1-t)}
$$

is the standard smooth transition: it lies in $[0,1]$, is zero for $t\le0$, and one for $t\ge1$.

Given $x\in U_i$, choose $r>0$ with $B(x,r)\subset U_i$ and set

$$
h(y)=\eta\left(\frac{(r/2)^2-\|y-x\|^2}{(r/2)^2-(r/4)^2}\right).
$$

The denominator is positive. The squared norm is smooth, so $h$ is globally smooth. It equals one on $B(x,r/4)$ and vanishes when $\|y-x\|\ge r/2$. Its support is a closed subset of the compact ball $\overline B(x,r/2)$, which is contained in $U_i$. Finite extraction gives bumps covering $K$. Apply the same ordered-product formula as in Exercise 10.5. Finite products preserve smoothness; support containment preserves compact support and subordination. The telescoping product proves the sum condition. Smoothness implies differentiability.

The source contains this construction, but `R10E06.smooth_partition` remains marked in progress in the inventory.

**Lean declarations:** `Rudin.Chapter10.exercise06_source_glue`, `Rudin.Chapter10.exercise06_transition_eq`, `Rudin.Chapter10.exercise06_auxiliary_smooth`, `Rudin.Chapter10.exercise06_bump`, `Rudin.Chapter10.exercise06_product_smooth`, `Rudin.Chapter10.exercise06_smooth_partition`.

<a id="r10e07"></a>
### 10.7 — The standard simplex as a convex hull

**Lean source:** [Exercise07.lean](../../Math/Rudin/Chapter10/Exercise07.lean).

**Inventory status:** Verified as stated.

**Statement.** The closed standard simplex

$$
Q^n=\{x\in\mathbb R^n:x_i\ge0,\ \sum_i x_i\le1\}
$$

is the smallest convex set containing $0,e_1,\ldots,e_n$. Equivalently, it is their convex hull. The image of any convex set under any real affine map is convex, without openness or nonemptiness assumptions. The simplex assertion includes $n=0$.

**Proof.** Nonnegative convex combinations preserve each coordinate inequality and the inequality on the coordinate sum, so $Q^n$ is convex. It contains all the listed vertices. Conversely, for $x\in Q^n$,

$$
x=\left(1-\sum_i x_i\right)0+\sum_i x_i e_i.
$$

These weights are nonnegative and sum to one. Every convex set containing the vertices therefore contains $x$. When $n=0$, the only vertex and the only point of the simplex are zero. Finally, if $T$ is affine, then $T(ax+by)=aT(x)+bT(y)$ for $a,b\ge0$ with $a+b=1$. This proves convexity of the affine image.

**Lean declarations:** `Rudin.Chapter10.exercise07_convex`, `Rudin.Chapter10.exercise07_minimal`, `Rudin.Chapter10.exercise07_a`, `Rudin.Chapter10.exercise07_b`.

<a id="r10e08"></a>
### 10.8 — An exponential integral over a parallelogram

**Lean source:** [Exercise08.lean](../../Math/Rudin/Chapter10/Exercise08.lean).

**Inventory status:** Pending verification.

**Statement.** Let $H$ have vertices $(1,1),(3,2),(4,5),(2,4)$. The affine map

$$
T(u,v)=(1+2u+v,1+u+3v)
$$

sends the unit square onto $H$, takes $0,e_1,e_2$ to the prescribed vertices, and has Jacobian $5$. Moreover,

$$
\int_H e^{x-y}\,dx\,dy
=\int_{[0,1]^2}5e^{u-2v}\,du\,dv
=\frac52(e-1)(1-e^{-2}).
$$

The original integrand is integrable on $H$. The transformed square integrand also has an explicit repeated Darboux source integral with this value.

**Proof.** Write $T(u,v)=(1,1)+u(2,1)+v(1,3)$. This gives all four vertices and identifies its square image with the stated parallelogram, including its boundary. The actual derivative is the constant matrix

$$
\begin{pmatrix}2&1\\1&3\end{pmatrix},
$$

whose determinant is $6-1=5$. The same two linear equations show that $T$ is injective. Compactness of its square image and continuity of the exponential give integrability independently of the substitution. Change of variables applies to this injective differentiable map, and $T_1-T_2=u-2v$. Separating the exponential gives

$$
5\left(\int_0^1 e^u\,du\right)\left(\int_0^1 e^{-2v}\,dv\right)
=5(e-1)\frac{1-e^{-2}}2.
$$

Continuity on the square gives every stage of the transformed repeated Darboux integral, and the same one-dimensional calculation gives its value.

All four `R10E08` obligations remain todo with no mapped declarations, although the current file proves these results. The explicit source-integral witness is for the transformed square; the file expresses the original-region substitution as a measure-integral theorem, not as a separate source witness for the zero extension on $H$.

**Lean declarations:** `Rudin.Chapter10.Exercise08.vertices`, `Rudin.Chapter10.Exercise08.image_square`, `Rudin.Chapter10.Exercise08.affine_formula`, `Rudin.Chapter10.Exercise08.hasFDerivAt_transform`, `Rudin.Chapter10.Exercise08.jacobian`, `Rudin.Chapter10.Exercise08.injective`, `Rudin.Chapter10.Exercise08.integrand_transform`, `Rudin.Chapter10.Exercise08.transformed_integral`, `Rudin.Chapter10.Exercise08.integrable_integrand`, `Rudin.Chapter10.Exercise08.square_integral_value`, `Rudin.Chapter10.Exercise08.integral_value`, `Rudin.Chapter10.Exercise08.transformed_source`.

<a id="r10e09"></a>
### 10.9 — Polar integration and the correct slit

**Lean source:** [Exercise09.lean](../../Math/Rudin/Chapter10/Exercise09.lean).

**Inventory status:** Pending verification.

**Statement.** For $a\ge0$, let $D_a=\{(x,y):x^2+y^2\le a^2\}$ and $T(r,\theta)=(r\cos\theta,r\sin\theta)$. The image of $[0,a]\times[0,2\pi]$ is $D_a$. The map is injective on $(0,a)\times(0,2\pi)$, and its Jacobian is $r$. If $f$ is continuous on $D_a$, with real or complex values, then

$$
\int_{D_a}f(x,y)\,dx\,dy
=\int_0^a\left(\int_0^{2\pi}r f(r\cos\theta,r\sin\theta)\,d\theta\right)dr.
$$

The finite-disk measure identity also holds for real Banach-valued coefficients. For real $f$, the right side has explicit repeated Darboux witnesses; for complex $f$, such witnesses are supplied for both components. Continuous cutoffs with compact support in the open slit disk remove a compact-interior-support restriction. All assertions about integration include $a=0$.

The printed differential/bound assignment is not this formula. With its literal usual nested binding, $f=1$ and $a=1$ give $2\pi^2$ instead of $\pi$. The angular interval $(0,2\pi)$ requires a positive-$x$-axis slit, not the positive-$y$-axis slit in the hint.

**Proof.** The identity $\|T(r,\theta)\|_2^2=r^2$ proves containment. Conversely, represent $x+iy$ by its modulus and argument, adding $2\pi$ to negative arguments. Its modulus lies in $[0,a]$, and the adjusted angle lies in $[0,2\pi]$. This includes the origin. Shifting the angle by $-\pi$ and negating the target reduces injectivity on the open parameter rectangle to the standard polar chart. Differentiation gives columns $(\cos\theta,\sin\theta)$ and $(-r\sin\theta,r\cos\theta)$, with determinant $r$.

The map is also injective on $(0,a]\times(0,2\pi)$, whose image is the closed disk with the positive-$x$-axis radius removed. The omitted set is null; the proof bounds it by the horizontal coordinate line. Change of variables gives the disk integral as the integral of $r f(T(r,\theta))$ over this parameter set. Continuity on the compact closed disk proves integrability. The transformed integrand is continuous on the closed parameter rectangle and hence integrable there. Fubini and the irrelevance of interval endpoints give the displayed angular-inner, radial-outer formula.

For the approximation assertion, the open slit disk is the disk interior with that same radius removed. Its difference from the closed disk is null, since both the convex frontier and the slit are null. Exhaust the open slit by compact subsets and choose continuous cutoffs $0\le\chi_n\le1$, equal to one on each selected compact set and supported compactly inside the open slit. Every point of the open slit eventually has cutoff one. Although $f$ is assumed continuous only on the disk, each $\chi_nf$ is globally continuous: its support lies in the disk interior. Domination by $|f|$ proves convergence of the cutoff integrals to the full disk integral. Thus no boundary-vanishing hypothesis on $f$ is needed. At radius zero the disk is a null singleton and the radial integral is zero.

For the source witnesses, use coordinates $(\theta,r)$ on $[0,2\pi]\times[0,a]$ so that coordinate zero is integrated first. Continuity gives all real Darboux stages. Applying this to the real and imaginary parts and commuting those projections with integration gives the complex component statements.

Finally, the literal printed reading integrates $r$ from $0$ to $2\pi$ and the angle from $0$ to $1$, giving $2\pi^2$. The corrected unit-disk formula gives $\pi$. These values are unequal.

All five `R10E09` obligations remain todo and unmapped in the inventory. The file proves the geometry, correction, approximation, and measure identity above. Its explicit source witnesses concern the polar side, with component witnesses rather than a direct recursive complex tagged-sum predicate; no separate source witness for the disk zero extension is stated here.

**Lean declarations:** `Rudin.Chapter10.Exercise09.range`, `Rudin.Chapter10.Exercise09.interior_injective`, `Rudin.Chapter10.Exercise09.hasFDerivAt_transform`, `Rudin.Chapter10.Exercise09.jacobian`, `Rudin.Chapter10.Exercise09.image_slit`, `Rudin.Chapter10.Exercise09.slit_ae_disk`, `Rudin.Chapter10.Exercise09.disk_integral`, `Rudin.Chapter10.Exercise09.polar_integrable`, `Rudin.Chapter10.Exercise09.polar_integral`, `Rudin.Chapter10.Exercise09.slit_approximation`, `Rudin.Chapter10.Exercise09.polar_source_real`, `Rudin.Chapter10.Exercise09.polar_source_complex`, `Rudin.Chapter10.Exercise09.corrected_constant_value`, `Rudin.Chapter10.Exercise09.disk_area_one`, `Rudin.Chapter10.Exercise09.literal_value`, `Rudin.Chapter10.Exercise09.literal_order_obstruction`, `Rudin.Chapter10.Exercise09.literal_disk_obstruction`.

<a id="r10e10"></a>
### 10.10 — Decay, improper polar integration, and the Gaussian

**Lean source:** [Exercise10.lean](../../Math/Rudin/Chapter10/Exercise10.lean).

**Inventory status:** Pending verification.

**Statement.** A sufficient decay condition for a continuous real or complex function on the Euclidean plane is

$$
|f(x)|\le C(1+\|x\|)^{-q}\quad(x\in\mathbb R^2),\qquad C\ge0,\quad q>2.
$$

Under this condition, $f$ and $|f|$ are integrable. Integrals over expanding closed disks and coordinate squares $[-R,R]^2$ converge to the same plane integral, for both functions. Defining the improper polar integral by keeping the full angular interval at each radial cutoff gives

$$
\int_{\mathbb R^2}f
=\lim_{a\to\infty}\int_0^a\left(\int_0^{2\pi}r f(r\cos\theta,r\sin\theta)\,d\theta\right)dr,
$$

with absolute convergence in the same cutoff sense. In particular,

$$
\int_{\mathbb R}e^{-s^2}\,ds=\sqrt\pi,
\qquad
\lim_{R\to\infty}\int_{-R}^{R}e^{-s^2}\,ds=\sqrt\pi.
$$

Each finite one-dimensional Gaussian cut has a Darboux source integral. The printed reversed radial/angular binding instead gives a divergent Gaussian cutoff.

**Proof.** The standard integrability criterion for $(1+\|x\|)^{-q}$ in dimension two applies because $q>2$. The bound and continuity then prove integrability of $f$ and its norm. This includes $C=0$. Disks and coordinate squares are increasing measurable exhaustions of the plane. Convergence of set integrals of an integrable function proves agreement of their limits, also for the norm. The finite-disk formula from Exercise 10.9 identifies each nonnegative-radius disk integral with the correctly bound polar cutoff. Passing to the limit proves the polar formula and its absolute version.

For $G(x)=e^{-\|x\|^2}$, the source verifies the explicit decay bound $G(x)\le24(1+\|x\|)^{-4}$. It follows from the exponential power estimate and $(1+t)^4\le24e^{t^2}$ for $t\ge0$. In polar coordinates $G=e^{-r^2}$. The antiderivative $-e^{-r^2}/2$ gives

$$
\int_0^a r e^{-r^2}\,dr=\frac{1-e^{-a^2}}2,
\qquad
\int_0^a\int_0^{2\pi}r e^{-r^2}\,d\theta\,dr=\pi(1-e^{-a^2}).
$$

The limit is $\pi$, so the plane Gaussian integral is $\pi$. The one-dimensional Gaussian is integrable by the library integrability theorem. In Cartesian coordinates $G(x,y)=e^{-x^2}e^{-y^2}$; product integration gives $I^2=\pi$, where $I=\int_{\mathbb R}e^{-s^2}\,ds\ge0$. Thus $I=\sqrt\pi$. Continuity supplies the Darboux witness on every ordered finite interval, including singleton intervals. Integrability then identifies the symmetric finite-cut limit with $I$.

With the literal printed binding, the Gaussian cutoff is instead

$$
L(A)=\int_0^A\left(\int_0^{2\pi}r e^{-r^2}\,dr\right)d\theta
=A\frac{1-e^{-(2\pi)^2}}2.
$$

Its coefficient is positive. Hence $L(A)\to+\infty$ and it has no finite limit, unlike the corrected plane integral.

All four `R10E10` obligations remain todo and unmapped. The general improper integrals here are explicitly defined as limits of finite measure integrals, with their convergence proved. The file does not supply a separate literal repeated-Riemann comparison for every general decay function and every Cartesian cutoff; its direct finite source witnesses are for the one-dimensional Gaussian. This distinguishes the established improper-measure formulation from a broader source-integral certification.

**Lean declarations:** `Rudin.Chapter10.Exercise10.integrable_of_decay`, `Rudin.Chapter10.Exercise10.disk_exhaustion`, `Rudin.Chapter10.Exercise10.rectangle_exhaustion`, `Rudin.Chapter10.Exercise10.decay_convergence`, `Rudin.Chapter10.Exercise10.disk_polar`, `Rudin.Chapter10.Exercise10.whole_plane_polar`, `Rudin.Chapter10.Exercise10.absolute_polar_convergence`, `Rudin.Chapter10.Exercise10.gaussian_decay`, `Rudin.Chapter10.Exercise10.gaussian_polar`, `Rudin.Chapter10.Exercise10.radial_gaussian_integral`, `Rudin.Chapter10.Exercise10.gaussian_cutoff`, `Rudin.Chapter10.Exercise10.gaussian_plane_integral`, `Rudin.Chapter10.Exercise10.gaussian_integral`, `Rudin.Chapter10.Exercise10.gaussian_finite_source`, `Rudin.Chapter10.Exercise10.gaussian_improper`, `Rudin.Chapter10.Exercise10.literal_cutoff_value`, `Rudin.Chapter10.Exercise10.literal_order_obstruction`, `Rudin.Chapter10.Exercise10.literal_no_finite_value`.

<a id="r10e11"></a>
### 10.11 — The beta–gamma substitution

**Lean source:** [Exercise11.lean](../../Math/Rudin/Chapter10/Exercise11.lean).

**Inventory status:** Pending verification.

**Statement.** The map $T(s,t)=(s-st,st)$ is a bijection from $S=(0,\infty)\times(0,1)$ onto $Q=(0,\infty)^2$, with inverse $(u,v)\mapsto(u+v,v/(u+v))$ and Jacobian $s$. For an integrable coefficient on $Q$, substitution is valid on the full strip and along every increasing compact exhaustion of it. For $x,y>0$,

$$
\int_0^1 t^{x-1}(1-t)^{y-1}\,dt
=\frac{\Gamma(x)\Gamma(y)}{\Gamma(x+y)}.
$$

The beta integrand is absolutely integrable on $(0,1)$, including when it is unbounded near an endpoint. Each compact interior interval has a Darboux source integral. Those finite source values converge to the displayed value along any increasing compact-interval exhaustion of $(0,1)$.

**Proof.** For $s>0$ and $0<t<1$, both $s(1-t)$ and $st$ are positive. Conversely, $u,v>0$ give $s=u+v>0$ and $0<v/(u+v)<1$. Direct substitution verifies both inverse identities. Differentiation gives

$$
DT=\begin{pmatrix}1-t&-s\\t&s\end{pmatrix},\qquad \det DT=s.
$$

The injective differentiable change-of-variables theorem gives the measure-integral identity, and its integrability version gives

$$
f\in L^1(Q)\quad\Longleftrightarrow\quad s f(T(s,t))\in L^1(S).
$$

The convergence assertion assumes $f\in L^1(Q)$ and compact sets $K_n$ with $K_n\subset K_{n+1}$ and $\bigcup_nK_n=S$. Finite substitution holds on each $K_n$, and integrability makes both the transformed cut integrals and their image integrals tend to $\int_Q f$. Such compact exhaustions exist because the strip is open in the plane. Equality of totalized integrals alone is not used to infer convergence.

Put $g_z(u)=e^{-u}u^{z-1}$. To obtain the displayed beta integrand with this choice of $T$, the source uses the quadrant kernel $g_y(u)g_x(v)$. Its integral is $\Gamma(y)\Gamma(x)$ and it is integrable by the gamma-integral convergence theorem. The transformed kernel factors as

$$
s\,g_y(s-st)g_x(st)
=e^{-s}s^{x+y-1}t^{x-1}(1-t)^{y-1}.
$$

All bases are positive on the strip, so the real-power product rules apply. Product integration therefore gives

$$
\Gamma(x)\Gamma(y)=\Gamma(x+y)\int_0^1t^{x-1}(1-t)^{y-1}\,dt.
$$

Divide by $\Gamma(x+y)>0$. This derives the beta value from the substitution rather than invoking a beta–gamma evaluation theorem. Transported integrability of the two-dimensional kernel, followed by integration in $s$, shows that $\Gamma(x+y)$ times the beta integrand is integrable; division by this positive constant proves beta integrability. Endpoints have measure zero, so the open-interval and interval-integral values agree.

On $[a,b]\subset(0,1)$, the integrand is continuous for arbitrary real exponents, and hence has the literal Darboux integral. For $x,y>0$, integrability and increasing exhaustion by such intervals prove convergence of these source values, including all singular endpoint cases allowed by the strict positivity assumptions.

All four `R10E11` obligations remain todo and unmapped. The full-strip change of variables and compact-exhaustion extension are measure-integral statements with explicit integrability hypotheses. The file additionally proves the one-dimensional improper beta source bridge; it does not state a general multidimensional source-Riemann theorem for arbitrary integrable coefficients on arbitrary compact exhaustion sets.

**Lean declarations:** `Rudin.Chapter10.Exercise11.bijection`, `Rudin.Chapter10.Exercise11.left_inverse`, `Rudin.Chapter10.Exercise11.right_inverse`, `Rudin.Chapter10.Exercise11.hasFDerivAt_transform`, `Rudin.Chapter10.Exercise11.jacobian`, `Rudin.Chapter10.Exercise11.integral_transform`, `Rudin.Chapter10.Exercise11.integrable_transform_iff`, `Rudin.Chapter10.Exercise11.improper_extension`, `Rudin.Chapter10.Exercise11.exists_strip_exhaustion`, `Rudin.Chapter10.Exercise11.kernel_transform`, `Rudin.Chapter10.Exercise11.quadrant_integrable`, `Rudin.Chapter10.Exercise11.quadrant_integral`, `Rudin.Chapter10.Exercise11.beta_gamma_Ioo`, `Rudin.Chapter10.Exercise11.beta_gamma`, `Rudin.Chapter10.Exercise11.strip_kernel_integrable`, `Rudin.Chapter10.Exercise11.beta_integrable`, `Rudin.Chapter10.Exercise11.beta_source_cut`, `Rudin.Chapter10.Exercise11.beta_source_improper`.

<a id="r10e12"></a>
### 10.12 — A triangular map from the cube to the simplex

**Lean source:** [Exercise12.lean](../../Math/Rudin/Chapter10/Exercise12.lean).

**Inventory status:** Pending verification.

**Statement.** Define, in source coordinate order,

$$
x_i=T(u)_i=u_i\prod_{j<i}(1-u_j),\qquad
S(x)_i=\frac{x_i}{1-\sum_{j<i}x_j}.
$$

Then

$$
\sum_{i=1}^n x_i=1-\prod_{i=1}^n(1-u_i),\qquad
T([0,1]^n)=Q^n.
$$

The map is injective on the cube interior and maps that interior bijectively onto the simplex interior, with inverse $S$. On the entire closed simplex, $S$ is a chosen right inverse of $T$, using value zero for a quotient whose denominator is zero. The actual Jacobians are

$$
J_T(u)=\prod_{i=1}^{n-1}(1-u_i)^{n-i},\qquad
J_S(x)=\left[\prod_{i=1}^{n-1}\left(1-\sum_{j=1}^{i}x_j\right)\right]^{-1},
$$

where the second formula is asserted on the simplex interior. The forward formula holds for all $u$. Empty sums and products cover $n=0$ and $n=1$; both determinants are $1$ in these cases.

**Proof.** Expanding the ordered product $\prod_i(1-u_i)$ by successive subtraction gives the sum identity. The same identity on each initial segment gives

$$
1-\sum_{j<i}T(u)_j=\prod_{j<i}(1-u_j).
$$

For $u\in[0,1]^n$, all coordinates of $T(u)$ are nonnegative, and the full sum is at most one. Conversely, for $x\in Q^n$, let $R_i=1-\sum_{j<i}x_j$. Nonnegativity of the remaining coordinates gives $0\le x_i\le R_i$. Thus $x_i/R_i\in[0,1]$ when $R_i>0$; when $R_i=0$, one also has $x_i=0$ and the chosen quotient is zero. Induction on $i$, using the prefix identity and previously recovered coordinates, proves $T(S(x))=x$ on the whole closed simplex. This proves closed-domain surjectivity without dividing by a zero denominator.

On the open cube, every prefix product is positive, so the same identity permits cancellation and gives $S(T(u))=u$. The forward coordinates are positive and their sum is strictly less than one. Conversely, the strict simplex inequalities give $0<x_i<R_i$, so $S(x)$ lies in the open cube. These sets are the actual topological interiors: the strict inequalities define open subsets, while a point in the closed simplex interior must have positive coordinates; a small positive change in one coordinate also forces its sum to be strictly less than one. Dimension zero is handled separately in this last argument.

The product and reciprocal differentiation rules give genuine Fréchet derivatives. Their matrices are lower triangular. The forward diagonal entry in row $i$ is $\prod_{j<i}(1-u_j)$, so multiplication of diagonal entries counts each factor $1-u_j$ exactly $n-j$ times. The inverse diagonal entry is $R_i^{-1}$. Its first denominator is one, leaving precisely the displayed product through $n-1$. Positivity of the denominators justifies differentiation of $S$ on the interior.

All six `R10E12` obligations remain marked in progress, although the current source includes the closed boundary and interior results above.

**Lean declarations:** `Rudin.Chapter10.Exercise12.coordinate_sum`, `Rudin.Chapter10.Exercise12.surjectivity`, `Rudin.Chapter10.Exercise12.S_mem_cube`, `Rudin.Chapter10.Exercise12.T_S`, `Rudin.Chapter10.Exercise12.S_T`, `Rudin.Chapter10.Exercise12.interior_injectivity`, `Rudin.Chapter10.Exercise12.injective_on_interior`, `Rudin.Chapter10.Exercise12.openCube_eq_interior`, `Rudin.Chapter10.Exercise12.interior_inverse`, `Rudin.Chapter10.Exercise12.openSimplex_eq_interior`, `Rudin.Chapter10.Exercise12.T_mem_openSimplex`, `Rudin.Chapter10.Exercise12.S_mem_openCube`, `Rudin.Chapter10.Exercise12.forward_jacobian`, `Rudin.Chapter10.Exercise12.hasFDerivAt_T`, `Rudin.Chapter10.Exercise12.inverse_jacobian`, `Rudin.Chapter10.Exercise12.hasFDerivAt_S`.

<a id="r10e13"></a>
### 10.13 — Monomial moments and simplex volume

**Lean source:** [Exercise13.lean](../../Math/Rudin/Chapter10/Exercise13.lean).

**Inventory status:** Pending verification.

**Statement.** For nonnegative integers $r_1,\ldots,r_n$ and $q$, the current source proves the stronger barycentric moment formula

$$
\int_{Q^n}\left(\prod_{i=1}^n x_i^{r_i}\right)\left(1-\sum_{i=1}^n x_i\right)^q dx
=\frac{\left(\prod_{i=1}^n r_i!\right)q!}{\left(n+\sum_{i=1}^n r_i+q\right)!}.
$$

In particular,

$$
\int_{Q^n}\prod_i x_i^{r_i}\,dx
=\frac{\prod_i r_i!}{(n+\sum_i r_i)!},\qquad
\operatorname{vol}(Q^n)=\frac1{n!}.
$$

The monomial is integrable. Its literal zero extension to the unit cube has repeated Darboux integrals in every coordinate order and a multidimensional tagged Riemann integral, all with the stated monomial value. Dimension zero and zero exponents are included.

**Proof.** The beta–gamma theorem at positive integer parameters gives

$$
\int_0^1 t^p(1-t)^q\,dt=\frac{p!q!}{(p+q+1)!}.
$$

Scaling the polynomial integral yields, for every real $a$,

$$
\int_0^a t^p(a-t)^q\,dt
=a^{p+q+1}\frac{p!q!}{(p+q+1)!}.
$$

This includes $a=0$ and uses oriented interval integration when $a<0$.

Induct on the dimension for the stronger moment formula. Separate the first coordinate $t$ from the remaining coordinates $z\in Q^{n-1}$, and write $a=1-\sum z_i\ge0$. The simplex slicing theorem gives the inner integral

$$
\left(\prod_{i=2}^n z_i^{r_i}\right)\int_0^a t^{r_1}(a-t)^q\,dt
=\left(\prod_{i=2}^n z_i^{r_i}\right)a^{r_1+q+1}
\frac{r_1!q!}{(r_1+q+1)!}.
$$

Apply the induction hypothesis with final barycentric exponent $r_1+q+1$. The factorial $(r_1+q+1)!$ cancels, giving the displayed formula. A slice with $a=0$ causes no exception. In dimension zero the domain has its normalized singleton measure, the empty monomial is one, and both sides equal one.

Taking $q=0$ gives the monomial formula; taking every $r_i=0$ gives volume. Continuity on the compact simplex proves integrability independently of the evaluated total integral. The local support results for the simplex zero extension supply every source Darboux stage, preserve the actual boundary values, and identify every permuted order with the set integral. The tagged-box comparison gives the multidimensional Riemann witness with the same value.

Both `R10E13` obligations remain marked in progress in the inventory.

**Lean declarations:** `Rudin.Chapter10.Exercise13.beta_natural`, `Rudin.Chapter10.Exercise13.beta_scaled`, `Rudin.Chapter10.Exercise13.mixed_moment`, `Rudin.Chapter10.Exercise13.monomial_integral`, `Rudin.Chapter10.Exercise13.monomial_integrable`, `Rudin.Chapter10.Exercise13.monomial_source`, `Rudin.Chapter10.Exercise13.monomial_riemann`, `Rudin.Chapter10.Exercise13.simplex_volume`.

<a id="r10e14"></a>
### 10.14 — The wedge sorting sign equals the determinant sign

**Lean source:** [Exercise14.lean](../../Math/Rudin/Chapter10/Exercise14.lean).

**Inventory status:** Pending verification.

**Statement.** Let $j=(j_1,\ldots,j_k)$ be coordinate indices and $\sigma$ a permutation of their positions. Define $s(\sigma)$ as the determinant of the corresponding permutation matrix. Then

$$
dx_{j_{\sigma(1)}}\wedge\cdots\wedge dx_{j_{\sigma(k)}}
=s(\sigma)\,dx_{j_1}\wedge\cdots\wedge dx_{j_k},
\qquad s(\sigma)=\operatorname{sgn}(\sigma).
$$

Thus the sign obtained by sorting distinct coordinate differentials is the determinant sign in the source equation. A transposition of distinct positions negates the wedge. The permutation identity also applies to repeated coordinate indices, when the alternating wedge vanishes, and to the empty wedge.

**Proof.** Regard each $dx_i$ as the coordinate covector and their wedge as the canonical alternating multilinear product in the exterior algebra of the dual space. The alternating-map permutation law multiplies this product by the permutation sign. The determinant permutation law gives exactly the same sign for the row-permuted identity matrix, since the identity determinant is one. This identifies the two definitions of sign. The alternating-map interchange law gives the transposition assertion directly. Alternation also makes a tuple with equal covectors in distinct positions vanish, so repeated indices introduce no exception.

`R10E14.permutation_sign` remains marked in progress in the inventory.

**Lean declarations:** `Rudin.Chapter10.Exercise14.permutation_sign`, `Rudin.Chapter10.Exercise14.determinantSign_eq`, `Rudin.Chapter10.Exercise14.interchange`.

<a id="r10e15"></a>
### 10.15 — Graded commutation of differential forms

**Lean source:** [Exercise15.lean](../../Math/Rudin/Chapter10/Exercise15.lean).

**Inventory status:** Pending verification.

**Statement.** If $\omega$ is a real $k$-form and $\lambda$ a real $m$-form on a common domain, then

$$
\omega\wedge\lambda=(-1)^{km}\lambda\wedge\omega.
$$

The wedge has degree $k+m$. Products of coordinate wedges with a repeated index vanish. Forms are represented as sections of homogeneous exterior powers of the dual space, and the wedge is actual exterior-algebra multiplication. The result is pointwise: it requires neither coefficient regularity nor an open domain, and it includes degree zero. More generally, the homogeneous-element identity holds in the exterior algebra of any real module.

**Proof.** First consider decomposable homogeneous elements $a=u_1\wedge\cdots\wedge u_k$ and $b=v_1\wedge\cdots\wedge v_m$. Moving the first block past the second makes $km$ interchanges, so the exterior-algebra anticommutation law gives $ab=(-1)^{km}ba$. The source uses this standard law for the canonical alternating products. Such products span each homogeneous exterior power. Bilinearity, addition, and compatibility with scalar multiplication extend the identity by induction on these spans to arbitrary homogeneous elements.

Apply that identity to $\omega(x)$ and $\lambda(x)$ at every point $x$. The source first states the sign using integer units, then converts it to the literal real scalar $(-1)^{km}$. Multiplication of the degree-$k$ and degree-$m$ submodules lies in the degree-$(k+m)$ submodule. If one factor in the first block equals one factor in the second, their concatenated tuple has two equal entries in distinct positions. Its alternating product is zero, proving the repeated-index assertion without a distinctness restriction on the original tuples.

`R10E15.graded_commutation` remains marked in progress in the inventory.

**Lean declarations:** `Rudin.Chapter10.Exercise15.homogeneous_commutation`, `Rudin.Chapter10.Exercise15.graded_commutation`, `Rudin.Chapter10.Exercise15.graded_commutation_real`, `Rudin.Chapter10.Exercise15.wedge_mem`, `Rudin.Chapter10.Exercise15.wedge_repeated_index`.

<a id="r10e16"></a>
### 10.16 — The boundary of a boundary

**Lean source:** [Exercise16.lean](../../Math/Rudin/Chapter10/Exercise16.lean).

**Inventory status:** Pending verification.

**Statement.** For an oriented affine simplex $\sigma=[p_0,\ldots,p_k]$ of dimension $k\geq2$, the alternating face boundary satisfies $\partial^2\sigma=0$. The same identity holds for every finite integer chain. In the ordinary, unaugmented convention, a zero-chain has zero boundary, so the identity also includes dimensions zero and one. These statements also hold for chains of full parameter maps, not only affine vertex lists. The algebraic result requires no differentiability assumption.

**Proof.** The boundary is

$$
\partial[p_0,\ldots,p_k]=\sum_{i=0}^k(-1)^i[p_0,\ldots,\widehat p_i,\ldots,p_k].
$$

For $i<j$, deleting $p_i$ and then $p_j$ has sign $(-1)^{i+j-1}$, whereas deleting $p_j$ and then $p_i$ has sign $(-1)^{i+j}$. Both operations give the same ordered face. Thus every term cancels with its other occurrence. In the ordered-list proof this cancellation is encoded by $\partial(a*c)=c-a*\partial c$ and induction. It holds before the orientation quotient and therefore after it. Additivity extends it to all signed chains, including all integer multiplicities.

For full maps, a face is restriction along the affine inclusion that omits a parameter vertex. The two deletion orders give equal full composite maps, and the same fixed-point-free pairing cancels the signed terms. Restriction commutes with arbitrary postcomposition, and the boundary commutes with both postcomposition and integer multiplication. This includes differentiable maps without imposing an extra $C^2$ condition.

The comparison with the source simplex is exact on the closed domain. If $u_i\geq0$ and $\sum u_i\leq1$, its barycentric coordinates are $(1-\sum u_i,u_1,\ldots,u_k)$. Every nonnegative barycentric tuple of sum one arises this way, and its realization is $p_0+\sum u_i(p_i-p_0)$. Inserting a zero weight realizes the deleted-vertex face. Consequently the Cartesian and barycentric ranges agree, including their boundaries, and every parameter face remains in the closed simplex. The empty-list generator belongs only to the augmented auxiliary model; the ordinary boundary in degree zero is the zero map.

**Lean declarations:** `Rudin.Chapter10.Exercise16.source_boundary`, `Rudin.Chapter10.Exercise16.deleted_pairs_cancel`, `Rudin.Chapter10.Exercise16.simplex_boundary_squared`, `Rudin.Chapter10.Exercise16.chain_boundary_squared`, `Rudin.Chapter10.Exercise16.ordinary_second_boundary`, `Rudin.Chapter10.Exercise16.zero_chain_boundary`, `Rudin.Chapter10.Exercise16.source_face`, `Rudin.Chapter10.Exercise16.barycentric_surjective`, `Rudin.Chapter10.Exercise16.source_range`, `Rudin.Chapter10.Exercise16.Parameterized.face_face`, `Rudin.Chapter10.Exercise16.Parameterized.boundary_squared`, `Rudin.Chapter10.Exercise16.Parameterized.ordinaryBoundary_squared`, `Rudin.Chapter10.Exercise16.Parameterized.boundary_multiplicity`, `Rudin.Chapter10.Exercise16.Parameterized.boundary_map`, `Rudin.Chapter10.Exercise16.Parameterized.source_face`, `Rudin.Chapter10.Exercise16.Parameterized.source_map`, `Rudin.Chapter10.Exercise16.Parameterized.face_domain`.

<a id="r10e17"></a>
### 10.17 — Two oriented triangles form a square

**Lean source:** [Exercise17.lean](../../Math/Rudin/Chapter10/Exercise17.lean).

**Inventory status:** Pending verification.

**Statement.** Set $q_0=(0,0)$, $q_1=(1,0)$, $q_2=(1,1)$, $q_3=(0,1)$, and let $\tau_1=[q_0,q_1,q_2]$, $\tau_2=-[q_0,q_3,q_2]$. Their sum $J^2$ is the positively oriented unit square: their closed ranges cover the square and have disjoint interiors. Its boundary is

$$
\partial J^2=[q_0,q_1]+[q_1,q_2]+[q_2,q_3]+[q_3,q_0].
$$

In contrast,

$$
\partial(\tau_1-\tau_2)=[q_0,q_1]+[q_1,q_2]+[q_0,q_3]+[q_3,q_2]-2[q_0,q_2].
$$

**Proof.** The first affine triangle has range $0\leq y\leq x\leq1$: the inverse barycentric weights are $(1-x,x-y,y)$. The second has range $0\leq x\leq y\leq1$, with weights $(1-y,y-x,x)$. These formulas retain the diagonal, edges, and vertices. The two possible orders of $x,y$ prove coverage. An interior point of a region constrained by $x\leq y$ must satisfy $x<y$: the nonzero linear map $(x,y)\mapsto x-y$ is open, so the interior maps into the interior of $(-\infty,0]$. Applying this to both triangles proves disjointness of their interiors.

The two vertex-difference matrices have determinants $1$ and $-1$. The coefficient $-1$ in $\tau_2$ therefore makes both signed triangles positive; it does not change their geometric ranges. Expand each triangle boundary. In the sum the diagonal cancels and reversed outer edges acquire their cyclic signs. In the difference the diagonal occurs with coefficient $-2$, which gives the second displayed formula.

**Lean declarations:** `Rudin.Chapter10.Exercise17.lower_range`, `Rudin.Chapter10.Exercise17.upper_range`, `Rudin.Chapter10.Exercise17.range₁`, `Rudin.Chapter10.Exercise17.range₂`, `Rudin.Chapter10.Exercise17.square_coverage`, `Rudin.Chapter10.Exercise17.interior_coordinate_lt`, `Rudin.Chapter10.Exercise17.disjoint_interiors`, `Rudin.Chapter10.Exercise17.positive_orientations`, `Rudin.Chapter10.Exercise17.J2_value`, `Rudin.Chapter10.Exercise17.square_boundary`, `Rudin.Chapter10.Exercise17.difference_boundary`.

<a id="r10e18"></a>
### 10.18 — Six tetrahedra form a cube

**Lean source:** [Exercise18.lean](../../Math/Rudin/Chapter10/Exercise18.lean).

**Inventory status:** Pending verification.

**Statement.** For each permutation $p=(i,j,k)$ of $(1,2,3)$, take

$$
\sigma_p=\operatorname{sgn}(p)[0,e_i,e_i+e_j,e_1+e_2+e_3].
$$

All six signed tetrahedra have positive orientation. Their ranges cover $[0,1]^3$ with pairwise disjoint interiors, and the range in order $(1,2,3)$ is $0\leq x_3\leq x_2\leq x_1\leq1$. The boundary of their sum $J^3$ consists of twelve oriented triangles on the six square faces.

**Proof.** The six orders $123,132,213,231,312,321$ have signs $+,-,-,+,+,-$ and exhaust all permutations exactly once. The cumulative-sum vertex matrix has the determinant of the corresponding permutation matrix. The first determinant is $1$; multiplying any determinant by its prescribed sign gives $1$.

For order $(i,j,k)$, the affine coordinates of barycentric weights are $(w_1+w_2+w_3,w_2+w_3,w_3)$ in that order. Thus its exact range is $0\leq x_k\leq x_j\leq x_i\leq1$. Conversely, such a point has weights

$$
(1-x_i,\ x_i-x_j,\ x_j-x_k,\ x_k).
$$

Sorting three real coordinates proves cube coverage, including ties and coordinates zero or one. Interior points have strict coordinate order, by the open-linear-map argument of Exercise 17. Different orders cannot both hold strictly, so the interiors are disjoint.

Write $S(a,b,c,d)=[a,b,c]-[a,d,c]$ and $s=e_1+e_2+e_3$. Expanding the twenty-four signed faces gives

$$
\begin{aligned}
\partial J^3={}&S(e_1,e_1+e_2,s,e_1+e_3)-S(0,e_2,e_2+e_3,e_3)\\
&-S(e_2,e_1+e_2,s,e_2+e_3)+S(0,e_1,e_1+e_3,e_3)\\
&+S(e_3,e_1+e_3,s,e_2+e_3)-S(0,e_1,e_1+e_2,e_2).
\end{aligned}
$$

The twelve internal face occurrences cancel in pairs, leaving two triangles on each coordinate face. More precisely, insert $r$ into coordinate $i$ of each of the two triangle maps from Exercise 17. Affine realization commutes with this insertion. Their combined range is exactly $x_i=r$ with the remaining coordinates in $[0,1]$. Taking $r=0,1$ gives exactly the cube surface, including all edges and corners. This establishes geometric coverage as well as the chain identity.

**Lean declarations:** `Rudin.Chapter10.Exercise18.order_bijective`, `Rudin.Chapter10.Exercise18.all_permutations`, `Rudin.Chapter10.Exercise18.vertices_permutation`, `Rudin.Chapter10.Exercise18.sign_determinant`, `Rudin.Chapter10.Exercise18.first_orientation`, `Rudin.Chapter10.Exercise18.positive_orientations`, `Rudin.Chapter10.Exercise18.coordinates`, `Rudin.Chapter10.Exercise18.range_iff`, `Rudin.Chapter10.Exercise18.first_range`, `Rudin.Chapter10.Exercise18.cube_coverage`, `Rudin.Chapter10.Exercise18.interior_order`, `Rudin.Chapter10.Exercise18.disjoint_interiors`, `Rudin.Chapter10.Exercise18.J3_value`, `Rudin.Chapter10.Exercise18.cube_boundary`, `Rudin.Chapter10.Exercise18.faceTriangle_realize`, `Rudin.Chapter10.Exercise18.face_coverage`, `Rudin.Chapter10.Exercise18.surface_coverage`.

<a id="r10e19"></a>
### 10.19 — The alternating cube-face formula

**Lean source:** [Exercise19.lean](../../Math/Rudin/Chapter10/Exercise19.lean).

**Inventory status:** Pending verification.

**Statement.** Define the affine coordinate insertions $B_{r1}(u,v)=(r,u,v)$, $B_{r2}(u,v)=(u,r,v)$, $B_{r3}(u,v)=(u,v,r)$, and let $\beta_{ri}=B_{ri}(J^2)$ as an oriented affine two-chain. Then

$$
\partial J^3=\sum_{i=1}^3(-1)^i(\beta_{0i}-\beta_{1i}).
$$

This is equality of chains, with their signs and multiplicities, not only equality of ranges or integral values.

**Proof.** Affine maps preserve barycentric combinations of weights summing to one. Thus mapping the vertices by $B_{ri}$ is exactly postcomposition of each full affine triangle map. In particular, $\beta_{ri}$ is the square chain on the four inserted vertices, or equivalently the first inserted triangle minus the second inserted triangle. Substitute these six square chains in the boundary expansion from Exercise 18. The faces with fixed first and third coordinates occur as upper minus lower, and the faces with fixed second coordinate as lower minus upper. These are precisely the signs in the displayed formula. The formal indexing starts at zero, so its exponent is the coordinate index plus one.

**Lean declarations:** `Rudin.Chapter10.Exercise19.insertion_formulas`, `Rudin.Chapter10.Exercise19.insertion_realize`, `Rudin.Chapter10.Exercise19.β_value`, `Rudin.Chapter10.Exercise19.β_triangles`, `Rudin.Chapter10.Exercise19.face_chain_value`, `Rudin.Chapter10.Exercise19.face_triangles`, `Rudin.Chapter10.Exercise19.cube_face_formula`.

<a id="r10e20"></a>
### 10.20 — Integration by parts for differential forms

**Lean source:** [Exercise20.lean](../../Math/Rudin/Chapter10/Exercise20.lean).

**Inventory status:** Verified as stated.

**Statement.** Let $U$ be open in a real normed space, $f:U\to\mathbb R$ be $C^1$, and $\omega$ be a $C^1$ differential $n$-form on $U$. Let $\Phi$ be a finite integer chain of $(n+1)$-simplex maps, each $C^2$ on an open neighborhood of its closed parameter simplex, whose entire closed images lie in $U$. With the signed restriction boundary,

$$
\int_\Phi f\,d\omega=\int_{\partial\Phi}f\omega-\int_\Phi df\wedge\omega.
$$

Every coefficient integral and each boundary-face integral exists; the simplex integrals also have the source repeated Riemann interpretation in every coordinate order. The formula descends to the oriented quotient for any chain with such an admissible representative. It includes zero chains and integer multiplicities.

**Proof.** The differential wedge is the usual unnormalized alternation:

$$
(df\wedge\omega)_x(v_0,\ldots,v_n)=\sum_{i=0}^n(-1)^i df_x(v_i)\,\omega_x(v_0,\ldots,\widehat v_i,\ldots,v_n).
$$

The derivative product rule and linearity of alternation give $d(f\omega)=f\,d\omega+df\wedge\omega$. Both summands and $f\omega$ are continuous on $U$. Their pullback coefficients are continuous on the compact closed parameter simplexes, including every face, which supplies integrability and the repeated Riemann witnesses. Apply Stokes to $f\omega$, split its integral using that integrability, and rearrange. Linearity extends the calculation from a simplex to the full integer chain. Integration and boundary respect the orientation relations, so the quotient statement follows from any admissible representative.

For $n=0$, take the zero-form $g$ on $\mathbb R$ and the affine segment from $a$ to $b$. Its one-form integral is the oriented interval integral; its zero-dimensional signed boundary evaluates to $f(b)g(b)-f(a)g(a)$, and $df\wedge g=g\,df$. Consequently, for globally $C^1$ real functions $f,g$ and any $a,b$,

$$
\int_a^b f(x)g'(x)\,dx=f(b)g(b)-f(a)g(a)-\int_a^b f'(x)g(x)\,dx.
$$

This holds for either endpoint order. For $a\leq b$, including $a=b$, both terms have actual Darboux Riemann integral witnesses, obtained from their continuous coefficients.

**Lean declarations:** `Rudin.Chapter10.Exercise20.validity_conditions`, `Rudin.Chapter10.Exercise20.continuous_terms`, `Rudin.Chapter10.Exercise20.differentialWedge_apply`, `Rudin.Chapter10.Exercise20.exterior_product`, `Rudin.Chapter10.Exercise20.form_identity`, `Rudin.Chapter10.Exercise20.oriented_form_identity`, `Rudin.Chapter10.Exercise20.differentialWedge_zero`, `Rudin.Chapter10.Exercise20.segment_integral`, `Rudin.Chapter10.Exercise20.segment_boundary`, `Rudin.Chapter10.Exercise20.one_variable_identity`, `Rudin.Chapter10.Exercise20.one_variable_case`.

<a id="r10e21"></a>
### 10.21 — The angular form and winding number

**Lean source:** [Exercise21.lean](../../Math/Rudin/Chapter10/Exercise21.lean).

**Inventory status:** Pending verification.

**Statement.** On $\mathbb R^2\setminus\{0\}$, identify $z=x+iy$ and define

$$
\eta=\frac{x\,dy-y\,dx}{x^2+y^2}.
$$

The form is $C^1$ and closed, and its integral on the positive circle $\gamma_r(t)=(r\cos t,r\sin t)$, $r>0$, $0\leq t\leq2\pi$, is $2\pi$. If a closed curve $\Gamma$ is $C^2$ on an open neighborhood of $[0,2\pi]$ and every segment $[\gamma_r(t),\Gamma(t)]$ avoids zero, then $\int_\Gamma\eta=2\pi$. In particular, for $a,b>0$,

$$
\int_0^{2\pi}\frac{ab}{a^2\cos^2t+b^2\sin^2t}\,dt=2\pi.
$$

Locally, $\eta=d(\arctan(y/x))$ wherever $x\ne0$, and $\eta=d(-\arctan(x/y))$ wherever $y\ne0$. There is no single differentiable real potential on the punctured plane. Finally, for every closed $C^1$ curve $\Gamma:[a,b]\to\mathbb C\setminus\{0\}$, $a\leq b$, with continuous derivative jet $v$ satisfying the genuine within-derivative condition at all points, including endpoints,

$$
\frac1{2\pi}\int_a^b\eta_{\Gamma(t)}(v(t))\,dt=\operatorname{Ind}(\Gamma).
$$

The index is exactly the Chapter 8 index. Source Darboux Riemann witnesses are supplied for this angular integral, for the circle, for the homotopy conclusion, and for the ellipse.

**Proof.** The angular covector satisfies $\eta_z(v)=\operatorname{Im}(v/z)$. On the circle, $\gamma_r'=(-r\sin t,r\cos t)$ and the quotient coefficient is identically one, proving the circle value. Direct differentiation of the two arctangent charts gives the displayed covector. Each chart is $C^2$ where its denominator is nonzero, so $d\eta=d^2\theta=0$ locally. At least one chart applies at every nonzero point. If a global differentiable potential existed, its composition with the unit circle would have derivative one. The fundamental theorem of calculus would then give a change of $2\pi$ between equal endpoint values, a contradiction.

For the Stokes proof, rescale the parameter rectangle positively to the unit square and use

$$
H(s,u)=(1-u)\Gamma(2\pi s)+u\gamma_r(2\pi s).
$$

The segment hypothesis puts its closed image in the punctured plane. It is $C^2$ near the parameter square. Triangulate that square into two actual smooth triangles, apply simplex Stokes and $d\eta=0$, and cancel the internal diagonal. The two side restrictions coincide because both curves are closed, so their integrals cancel. The remaining two restrictions give equality with the circle integral. Positive linear rescaling preserves these path integrals. For the ellipse, the straight segment to the unit circle has coordinates $((u+va)\cos t,(u+vb)\sin t)$ with $u,v\geq0$, $u+v=1$; both factors are positive. It cannot vanish because sine and cosine cannot both vanish. Its angular coefficient is the displayed rational function, so the homotopy result applies.

There is also a proof without Stokes. Segment avoidance implies $\Gamma(t)/\gamma_r(t)$ lies off the nonpositive real axis. On this slit domain, the half-angle primitive

$$
A(z)=2\arctan\frac{y}{\sqrt{x^2+y^2}+x}
$$

has derivative $\eta$. Its denominator is positive. Along the quotient curve its derivative is $\eta_{\Gamma(t)}(\Gamma'(t))-1$, by the quotient rule and the circle calculation. The quotient has equal endpoints, so the fundamental theorem of calculus makes the integral of this difference zero.

For the general $C^1$ loop, the logarithmic derivative $v/\Gamma$ is continuous on the closed interval and integrable. Chapter 8 proves that its integral is $2\pi i n$ for an integer $n$, and defines the index as that integral divided by $2\pi i$. Taking imaginary parts gives the asserted angular identity, including the singleton interval case. The full-map path integral on $[0,1]$ agrees with this expression whenever $v$ is the actual ambient derivative. Continuity of the real angular coefficients supplies all stated source Riemann integrals.

**Lean declarations:** `Rudin.Chapter10.Exercise21.eta_eq_im_div`, `Rudin.Chapter10.Exercise21.circle_integral`, `Rudin.Chapter10.Exercise21.circle_derivative`, `Rudin.Chapter10.Exercise21.circle_coefficient`, `Rudin.Chapter10.Exercise21.circle_source_integral`, `Rudin.Chapter10.Exercise21.eta_closed`, `Rudin.Chapter10.Exercise21.eta_smooth`, `Rudin.Chapter10.Exercise21.closed_triangle_boundary`, `Rudin.Chapter10.Exercise21.closed_square_boundary`, `Rudin.Chapter10.Exercise21.straight_homotopy_stokes`, `Rudin.Chapter10.Exercise21.straight_homotopy_source`, `Rudin.Chapter10.Exercise21.ellipse_integral`, `Rudin.Chapter10.Exercise21.ellipse_source_integral`, `Rudin.Chapter10.Exercise21.xAngle_exterior`, `Rudin.Chapter10.Exercise21.xAngle_derivative`, `Rudin.Chapter10.Exercise21.yAngle_exterior`, `Rudin.Chapter10.Exercise21.yAngle_derivative`, `Rudin.Chapter10.Exercise21.local_angles_not_global`, `Rudin.Chapter10.Exercise21.not_globally_exact`, `Rudin.Chapter10.Exercise21.straight_homotopy_local_primitives`, `Rudin.Chapter10.Exercise21.cutAngle_curve_derivative`, `Rudin.Chapter10.Exercise21.winding_index`, `Rudin.Chapter10.Exercise21.angularIntegral_source`, `Rudin.Chapter10.Exercise21.pathIntegral_bridge`, `Rudin.Chapter10.Exercise21.angularIntegral_eq_im`, `Rudin.Chapter10.Exercise21.integral_rescale`.

<a id="r10e23"></a>
### 10.23 — Radial forms: closedness and partial exactness coverage

**Lean source:** [Exercise23.lean](../../Math/Rudin/Chapter10/Exercise23.lean).

**Inventory status:** Pending verification.

**Statement.** For $1\leq k\leq N$, set $r_k=(\sum_{i=1}^k x_i^2)^{1/2}$ and $E_k=\{r_k>0\}$. The source radial form is

$$
\omega_k=r_k^{-k}\sum_{i=1}^k(-1)^{i-1}x_i\,dx_1\wedge\cdots\wedge\widehat{dx_i}\wedge\cdots\wedge dx_k.
$$

The completed source proves $d\omega_k=0$ on $E_k$ for every such $k$. For $k=1$ it also proves that $\omega_1=x_1/|x_1|$ is locally constant there. For $k\geq2$ and $-1<t<1$, it proves convergence, the derivative, and the improper-endpoint interpretation of

$$
g_k(t)=\int_{-1}^t(1-s^2)^{(k-3)/2}\,ds.
$$

In degree zero the added exactness convention is image $\{0\}$: a zero-form is exact on a domain if and only if it vanishes there. Positive-degree exactness means the exterior derivative of an actual $C^1$ form one degree lower. Under this explicit convention, the one-dimensional form on the punctured line is closed but not exact.

Further completed results concern sphere patches and radial rescaling. Let $K\subset\mathbb R^m$ be compact, $U$ an open neighborhood of $K$, and let $\sigma:U\to\mathbb R^{m+1}$ and $\rho:U\to\mathbb R$ be $C^2$, with $\|\sigma(u)\|=1$ and $\rho(u)>0$ on $K$. The two maps avoid zero on $K$, their pullbacks of $\omega_{m+1}$ agree on $K$, both flux coefficients are integrable over $K$, and their flux integrals over $K$ agree. No rank condition on $\sigma$ is required.

If additionally $K$ has unique differentiation at each point and the normal-first determinant $\det[\sigma,D_1\sigma,\ldots,D_m\sigma]$ is nonnegative on $K$, then its flux is its geometric parametric area

$$
\int_K\sqrt{\det\bigl(\langle D_i\sigma,D_j\sigma\rangle\bigr)}\,du.
$$

For a $C^2$ map from a neighborhood of a compact set of positive Lebesgue measure, this area is strictly positive if its parameter derivative columns are linearly independent at every point of that set.

This file has **partial source coverage**, not a complete solution. For `R10E23.b`, only the scalar integral facts above are proved; with the prescribed $f_k(x)=(-1)^k g_k(x_k/r_k)$, the identity $\omega_k=d(f_k\omega_{k-1})=df_k\wedge\omega_{k-1}$ on $E_{k-1}$ is not proved. For `R10E23.c`, nonexactness in dimensions at least two is not proved. For `R10E23.d.formulation` and `R10E23.d.generalization`, the results prove radial invariance and the sphere-patch flux/area comparison, but do not construct a whole-sphere chain, prove its face cancellation, or establish the global positive sphere integral required by the selected contract. The zero-degree convention is an explicit addition, not a source-defined negative-degree primitive.

**Proof.** In its own $k$ coordinates, write $\omega_k(x)=\|x\|^{-k}\iota_x\mathrm{vol}$; the ambient form is its pullback by projection to the first $k$ coordinates. Expanding the determinant in its first row proves the coordinate formula and the Euclidean norm formula proves the radius identity.

Alternation removes any multiple of the radial vector added to a tangent argument. Hence, for a positive scale $\rho$,

$$
\mathrm{vol}(\rho\sigma,\rho D_1\sigma+(D_1\rho)\sigma,\ldots)
=\rho^{m+1}\mathrm{vol}(\sigma,D_1\sigma,\ldots).
$$

The denominator scales by the same positive power. This proves radial pullback invariance, including nonconstant scales and rank-deficient maps. Apply it to normalization $x\mapsto x/\|x\|$, which preserves the form away from zero. Its derivative is tangent to the unit sphere: differentiation of the squared norm gives orthogonality to the unit radial vector. Any $k$ such tangent vectors in $\mathbb R^k$ are linearly dependent, since they lie in the proper kernel of a nonzero inner-product functional. Thus every top-degree alternating form vanishes on them. Naturality of exterior differentiation under the smooth normalization map now proves closedness, and pullback by the coordinate projection proves ambient closedness. For $k=1$, the sign function is constant on a neighborhood of each point of $E_1$, which also supplies derivative existence directly.

For $g_k$, the exponent $\alpha=(k-3)/2$ is greater than $-1$, including $\alpha=-1/2$ when $k=2$. Factor $(1-s^2)^\alpha=(1+s)^\alpha(1-s)^\alpha$. The first factor is integrable at $-1$; the second is continuous and bounded on $[-1,t]$. This proves endpoint integrability. The integrand is continuous at every interior $t$, so the fundamental theorem gives $g_k'(t)=(1-t^2)^\alpha$. Continuity of the interval primitive gives the limit of $\int_a^t$ as $a\downarrow-1$. No form-primitive identity follows in the current file.

For the degree-zero convention, evaluate the form at the first positive coordinate unit vector: its value is one. It therefore cannot be the zero form on $E_1$. At top index the radial domain is exactly punctured Euclidean space, so this also proves the stated punctured-line result. No negative-degree form is introduced.

For the area comparison, the square of the normal-first determinant is the Gram determinant of the normal and tangents. A unit normal orthogonal to the tangents makes this determinant equal to the tangent Gram determinant. Outward nonnegative orientation selects its nonnegative square root. Tangency on the compact domain, including boundary points, follows from the unit-norm identity and unique differentiation. This proves the pointwise flux-density identity. The $C^2$ neighborhood extensions give continuous area and flux densities; compactness gives their integrability and hence the integral identities. Linear independence makes the tangent Gram determinant positive, and positive measure then gives strictly positive area.

The file also checks normalization on the standard frame: the coordinate volume and the radial form on an outward orthonormal frame are one. A concrete radial-invariance example uses a constant unit direction and radius $1+\|u\|^2$ on any compact parameter set. These are normalization and rescaling checks, not a replacement for a whole-sphere integral.

**Lean declarations:** `Rudin.Chapter10.Exercise23.omega_source_formula`, `Rudin.Chapter10.Exercise23.radius_source_formula`, `Rudin.Chapter10.Exercise23.omega_closed`, `Rudin.Chapter10.Exercise23.topRadial_closed`, `Rudin.Chapter10.Exercise23.omega_one_apply`, `Rudin.Chapter10.Exercise23.omega_one_locally_constant`, `Rudin.Chapter10.Exercise23.omega_one_closed`, `Rudin.Chapter10.Exercise23.omega_one_not_exact`, `Rudin.Chapter10.Exercise23.g_integrable`, `Rudin.Chapter10.Exercise23.g_hasDerivAt`, `Rudin.Chapter10.Exercise23.g_improper_limit`, `Rudin.Chapter10.Exercise23.exactOn_zero_iff`, `Rudin.Chapter10.Exercise23.exactOn_zero_image`, `Rudin.Chapter10.Exercise23.exactOn_succ_iff`, `Rudin.Chapter10.Exercise23.dimension_one_closed_not_exact`, `Rudin.Chapter10.Exercise23.radialDomain_top`, `Rudin.Chapter10.Exercise23.radial_pullback_at`, `Rudin.Chapter10.Exercise23.normalize_pullback`, `Rudin.Chapter10.Exercise23.top_alternating_tangent_zero`, `Rudin.Chapter10.Exercise23.compact_radial_invariance`, `Rudin.Chapter10.Exercise23.normal_flux_eq_gram_area`, `Rudin.Chapter10.Exercise23.sphere_flux_density`, `Rudin.Chapter10.Exercise23.compact_sphere_flux_area`, `Rudin.Chapter10.Exercise23.parametricArea_pos`, `Rudin.Chapter10.Exercise23.coordinateVolume_standard`, `Rudin.Chapter10.Exercise23.topRadial_standard`, `Rudin.Chapter10.Exercise23.compact_radial_model`.

<a id="r10e28"></a>
### 10.28 — Stokes on a parametrized annulus

**Lean source:** [Exercise28.lean](../../Math/Rudin/Chapter10/Exercise28.lean).

**Inventory status:** Pending verification.

**Statement.** Let $0<a<b$, let $\Phi(r,\theta)=(r\cos\theta,r\sin\theta)$ on the closed rectangle $[a,b]\times[0,2\pi]$, with parameter order $(r,\theta)$, and put $\omega=x^3\,dy$. Then

$$
\int_\Phi d\omega=\int_{\partial\Phi}\omega=\frac{3\pi}{4}(b^4-a^4).
$$

The four induced parameter edges have integrals $0$, $3\pi b^4/4$, $0$, $-3\pi a^4/4$, respectively. The repeated surface integral with $r$ outermost, every angular slice, and all signed boundary integrals have source Riemann witnesses. The current source completes these results although the inventory declaration lists are still empty.

**Proof.** Differentiation gives $d\omega=3x^2\,dx\wedge dy$. The polar derivative has determinant $r$, so the pulled-back surface coefficient is $3r^3\cos^2\theta$. Also

$$
\Phi^*\omega=r^3\cos^3\theta\sin\theta\,dr+r^4\cos^4\theta\,d\theta.
$$

The standard trigonometric integral formulas give $\int_0^{2\pi}\cos^2\theta\,d\theta=\pi$ and $\int_0^{2\pi}\cos^4\theta\,d\theta=3\pi/4$. Integrating $3\pi r^3$ from $a$ to $b$ gives the surface value. On both radial edges the sine factor is zero, so their individual integrals vanish. Their image paths also coincide with opposite induced signs. On the outer circle the integral is $3\pi b^4/4$; the reversed inner circle gives $-3\pi a^4/4$. Their sum is the same surface value.

Independently of this numerical comparison, the proof applies rectangle Stokes to the actual pullback form. Naturality gives $d(\Phi^*\omega)=\Phi^*(d\omega)$, and Fubini identifies the continuous coefficient's area integral with the repeated integral. Its four induced boundary terms are exactly those just computed. The coefficient is continuous on the compact rectangle, so it is integrable; the same continuous-coefficient bridge gives each source Riemann witness. The algebraic numerical formulas hold for arbitrary real endpoints as oriented interval integrals. The area/Stokes comparison and source witnesses are proved for $a\leq b$, including $a=b$; the exercise theorem specializes to $0<a<b$. Finally $\|\Phi(r,\theta)\|^2=r^2$, which verifies the annular radius bounds on the closed domain.

**Lean declarations:** `Rudin.Chapter10.Exercise28.exterior`, `Rudin.Chapter10.Exercise28.polar_derivative`, `Rudin.Chapter10.Exercise28.pullback_value`, `Rudin.Chapter10.Exercise28.surface_coefficient`, `Rudin.Chapter10.Exercise28.angular_two`, `Rudin.Chapter10.Exercise28.angular_four`, `Rudin.Chapter10.Exercise28.surface_value`, `Rudin.Chapter10.Exercise28.radial_edges`, `Rudin.Chapter10.Exercise28.circular_edges`, `Rudin.Chapter10.Exercise28.boundary_value`, `Rudin.Chapter10.Exercise28.seam_paths`, `Rudin.Chapter10.Exercise28.annular_radius`, `Rudin.Chapter10.Exercise28.coefficient_integrable`, `Rudin.Chapter10.Exercise28.surface_area`, `Rudin.Chapter10.Exercise28.actual_stokes`, `Rudin.Chapter10.Exercise28.surface_source`, `Rudin.Chapter10.Exercise28.boundary_source`, `Rudin.Chapter10.Exercise28.exercise28`.

<a id="r10e29"></a>
### 10.29 — A smooth section and a varying-endpoint primitive

**Lean source:** [Exercise29.lean](../../Math/Rudin/Chapter10/Exercise29.lean).

**Inventory status:** Pending verification.

**Statement.** Let $X$ be a finite-dimensional real normed space and $V\subset X\times\mathbb R$ be open and convex. Its projection $U$ onto $X$ is open, and there is a $C^1$ function $\alpha:U\to\mathbb R$ with $(x,\alpha(x))\in V$. For $\varphi\in C^1(V)$,

$$
F(x,z)=\int_{\alpha(x)}^z\varphi(x,t)\,dt
$$

is $C^1$ on $V$, and each oriented fiber integral exists. The section is constructed, not assumed.

For the setting of Theorem 10.38, let $E\subset (X\times\mathbb R)\times Y$ be open and convex, where $Y$ is a real normed space, and let $f\in C^1(E)$ factor as $f((x,z),y)=\varphi(x,z)$. The constructed section on the projection of $E$ gives a $C^1$ primitive $F((x,z),y)$ on $E$ with all unused coordinates retained. For $p=1$, nonempty $E\subset\mathbb R\times Y$ supplies a fixed endpoint $c$ in its projection and the primitive $\int_c^x\varphi(t)\,dt$. On an empty domain regularity is vacuous; no endpoint in an empty projection is asserted. These completed results are not yet mapped in the inventory.

**Proof.** Each fiber of $V$ is a nonempty convex interval over its projection. For every $x\in U$, choose one fiber value $c_x$. Openness makes the same constant $c_x$ valid for all base points in a neighborhood of $x$. The smooth partition-of-unity selection theorem combines these locally constant choices into a locally finite smooth weighted sum. The weights sum to one, so convexity of each fiber keeps that sum in the fiber. This produces the $C^1$ section, also when $U$ is empty; an extension outside $U$ is used only to give a total function, without asserting smoothness outside $U$.

Convexity keeps the entire interval between $\alpha(x)$ and $z$ in the fiber, regardless of endpoint order. Use the affine substitution

$$
F(x,z)=\int_0^1(z-\alpha(x))\,\varphi\bigl(x,\alpha(x)+(z-\alpha(x))s\bigr)\,ds.
$$

It remains valid for equal or reversed endpoints. The integrand is $C^1$ near every point over the compact interval $0\leq s\leq1$. To justify differentiation under the integral, take a compact closed ball inside the open base domain. Continuity of the parameter derivative on its product with $[0,1]$ supplies a uniform bound. Dominated differentiation gives the derivative as the integral of that parameter derivative, and dominated continuity makes the derivative continuous. Thus the fixed-interval integral, and hence $F$, is $C^1$. The bound is derived locally, not an added global hypothesis. Continuity on each compact fiber interval gives integrability and Darboux Riemann witnesses. If the displayed bounds are $a>b$, the source witness on $[b,a]$ has value $-\int_a^b\varphi(x,t)\,dt$.

In the factorized setting, $\varphi$ is itself $C^1$ on the projection: near a projected point fix one admissible unused coordinate $y_0$ and use the local lift $z\mapsto(z,y_0)$ into $E$. The factorization identifies $\varphi$ locally with the $C^1$ function $f(z,y_0)$. Apply the preceding section and varying-integral results on the open convex projection, and compose with projection from $E$.

For $p=1$ and nonempty $E$, choose any point of $E$ and its first coordinate $c$. Convexity contains every integration interval in the projection. The fundamental theorem gives derivative $\varphi$ for $x\mapsto\int_c^x\varphi$, and continuity gives $C^1$ regularity. Compose with the first projection to retain unused coordinates. On the empty domain both the zero function and every fixed-endpoint displayed primitive are $C^1$ there, without a nonexistent choice from its projection.

**Lean declarations:** `Rudin.Chapter10.Exercise29.projection_open`, `Rudin.Chapter10.Exercise29.fiber_convex`, `Rudin.Chapter10.Exercise29.section_exists`, `Rudin.Chapter10.Exercise29.integral_c1_data`, `Rudin.Chapter10.Exercise29.integral_c1`, `Rudin.Chapter10.Exercise29.integral_hasFDerivAt`, `Rudin.Chapter10.Exercise29.fiber_interval`, `Rudin.Chapter10.Exercise29.integral_affine`, `Rudin.Chapter10.Exercise29.varying_integral_c1`, `Rudin.Chapter10.Exercise29.fiber_integrable`, `Rudin.Chapter10.Exercise29.fiber_source`, `Rudin.Chapter10.Exercise29.factor_c1`, `Rudin.Chapter10.Exercise29.exercise29`, `Rudin.Chapter10.Exercise29.fixed_lower_c1`, `Rudin.Chapter10.Exercise29.exercise29_p_one`, `Rudin.Chapter10.Exercise29.exercise29_empty`.

<a id="r10e30"></a>
### 10.30 — The Euclidean surface normal

**Lean source:** [Exercise30.lean](../../Math/Rudin/Chapter10/Exercise30.lean).

**Inventory status:** Verified as stated.

**Statement.** For arbitrary $\alpha,\beta\in\mathbb R^3$, let

$$
N=(\alpha_2\beta_3-\alpha_3\beta_2,\ \alpha_3\beta_1-\alpha_1\beta_3,\ \alpha_1\beta_2-\alpha_2\beta_1),\qquad T(u,v)=u\alpha+v\beta.
$$

Then $\det[\alpha\ \beta\ N]=\|N\|^2$, and $N\cdot T(e_1)=N\cdot T(e_2)=0$. The statements use the Euclidean inner product and norm and require no independence or nondegeneracy assumption.

**Proof.** The coordinate vector $N$ is $\alpha\times\beta$. The scalar triple-product identity gives

$$
\det[\alpha\ \beta\ N]=(\alpha\times\beta)\cdot N=N\cdot N=\|N\|^2.
$$

The cross product is perpendicular to each factor, so $N\cdot\alpha=N\cdot\beta=0$. The linear map $T$ sends the two parameter basis vectors to $\alpha$ and $\beta$, proving the stated orthogonality. These identities remain valid when the two factors are dependent, including zero vectors: the cross product then vanishes.

**Lean declarations:** `Rudin.Chapter10.exercise30_normal_coordinates`, `Rudin.Chapter10.exercise30_determinant`, `Rudin.Chapter10.exercise30_basis`, `Rudin.Chapter10.exercise30_normal_perpendicular`, `Rudin.Chapter10.exercise30_orthogonality`.

<a id="r10e32"></a>
### 10.32 — The Möbius band and its two boundary notions

**Lean source:** [Exercise32.lean](../../Math/Rudin/Chapter10/Exercise32.lean).

**Inventory status:** Pending verification.

**Statement.** Let $0<\delta<1$, $D=[0,\pi]\times[-\delta,\delta]$, and

$$
\Phi(\theta,t)=\bigl((1-t\sin\theta)\cos2\theta,\ (1-t\sin\theta)\sin2\theta,\ t\cos\theta\bigr).
$$

Its image is a regular Möbius band avoiding the $z$-axis. The only identifications are equal parameters and the reversed seam $\Phi(\pi,t)=\Phi(0,-t)$. It admits no continuous nowhere-zero normal field orthogonal to its actual parameter tangents.

Let $p_1=(0,-\delta)$, $p_2=(\pi,-\delta)$, $p_3=(\pi,\delta)$, $p_4=(0,\delta)$, $p_5=p_1$, and let $\Gamma_i$ be the full map $\Phi\circ[p_i,p_{i+1}]$, with its oriented affine unit-interval parametrization. Put $a=(1,0,-\delta)$ and $b=(1,0,\delta)$. Then $\Phi(p_1)=\Phi(p_3)=a$, $\Phi(p_2)=\Phi(p_4)=b$, and both $\Gamma_1,\Gamma_3$ run from $a$ to $b$. Their planar projections are loops with indices $+1,-1$, respectively. Both seam maps equal $[b,a]$, and the actual parameter boundary is

$$
\partial\Phi=\Gamma_1+\Gamma_2+\Gamma_3+\Gamma_4=\Gamma_1+\Gamma_3+2\Gamma_2.
$$

The single free rim instead has oriented chain $\Gamma=\Gamma_1-\Gamma_3$ and closed parametrization

$$
G(\theta)=\bigl((1+\delta\sin\theta)\cos2\theta,\ (1+\delta\sin\theta)\sin2\theta,\ -\delta\cos\theta\bigr),\qquad0\leq\theta\leq2\pi.
$$

For $\eta=(x\,dy-y\,dx)/(x^2+y^2)$, defined off the $z$-axis,

$$
\int_{\partial\Phi}\eta=0,\qquad\int_\Gamma\eta=\int_G\eta=4\pi.
$$

All four edge integrals and the displayed closed rim integral have source Riemann witnesses. Thus the free rim chain is not the parameter boundary chain.

**Proof.** Since $|t\sin\theta|\leq\delta<1$, the planar radius $1-t\sin\theta$ is positive on all of $D$, including its seam and rim. In particular the image avoids the $z$-axis. If two image points agree, their positive planar radii agree, and their planar angles $2\theta,2\psi$ have the same sine and cosine. For $\theta,\psi\in[0,\pi]$, this means either $\theta=\psi$ or the two opposite interval endpoints. In the first case equality of radius and height, together with $\sin^2\theta+\cos^2\theta=1$, gives equal transverse parameters. At the two endpoints it gives the reversed transverse parameter. Direct substitution proves the seam formula.

Differentiating $\Phi$ gives independent tangents everywhere on $D$. Indeed, in a relation $A\Phi_\theta+B\Phi_t=0$, the planar angular component is $2A(1-t\sin\theta)$, so $A=0$ by radius positivity. The transverse tangent has nonzero length, so $B=0$. This includes all boundary points.

To prove nonorientability, restrict a proposed continuous normal field to the core $c(\theta)=(\cos2\theta,\sin2\theta,0)$. Its two tangents are $(-2\sin2\theta,2\cos2\theta,0)$ and $(-\sin\theta\cos2\theta,-\sin\theta\sin2\theta,\cos\theta)$. Every vector perpendicular to both is a scalar multiple of the unit vector

$$
n(\theta)=(\cos\theta\cos2\theta,\cos\theta\sin2\theta,\sin\theta).
$$

The scalar is the dot product with $n(\theta)$ and is continuous and nonzero. But $c(0)=c(\pi)$ while $n(\pi)=-n(0)$, so its endpoint values are opposites. The intermediate value theorem forces a zero, a contradiction. This proves the stated normal-field formulation of nonorientability, not just a sign mismatch in a drawing.

Substitute the four corners to obtain their images. Rescale $D$ positively to the unit square by $(s,u)\mapsto(\pi s,\delta(2u-1))$. Its four signed full-map restrictions give the asserted boundary decomposition; the same boundary is obtained by triangulating the square into smooth simplexes. Substitution on the vertical edges shows that both are literally the same segment from $b$ to $a$. They therefore add with multiplicity two, rather than cancel. Endpoint substitution gives both rim arcs from $a$ to $b$.

The first half of $G$ is $\Gamma_1$ after positive linear rescaling, and the second half is the reverse of $\Gamma_3$. Splitting $[0,2\pi]$ at $\pi$ proves that its image is exactly the union of the two free-edge images, with no seam added. That union lies in the band, and $G(0)=G(2\pi)$.

The form $\eta$ is the pullback of the closed angular form of Exercise 21 by planar projection. It is $C^1$ off the axis and closed there. Apply analytic Stokes to the rescaled square, using its two smooth triangle maps and the axis-avoidance result, to obtain zero on its actual parameter boundary.

For direct values, a positive-radius planar curve of angular speed $k$ has angular coefficient $k$: the derivative of its radius contributes a radial vector, whose alternating numerator is zero. The first arc on the unit interval has coefficient $2\pi$, the third has coefficient $-2\pi$, and both seam coefficients are zero. Their source Riemann integrals are therefore $2\pi,0,-2\pi,0$. Exercise 21 identifies the two projected-loop indices as $+1$ and $-1$. The closed parametrization $G$ has coefficient $2$ throughout $[0,2\pi]$, giving $4\pi$ and its Riemann witness. Equivalently, the chain $\Gamma_1-\Gamma_3$ has integral $2\pi-(-2\pi)=4\pi$. Since integration is an additive function on these signed full-map chains, this nonzero value distinguishes it from the parameter boundary. There is no conflict with Stokes: the band is nonorientable, and its geometric free rim is not the signed boundary of this rectangular parametrization.

**Lean declarations:** `Rudin.Chapter10.Exercise32.seam`, `Rudin.Chapter10.Exercise32.injective_modulo_seam`, `Rudin.Chapter10.Exercise32.theta_derivative`, `Rudin.Chapter10.Exercise32.transverse_derivative`, `Rudin.Chapter10.Exercise32.tangent_independence`, `Rudin.Chapter10.Exercise32.avoids_axis`, `Rudin.Chapter10.Exercise32.nonorientable`, `Rudin.Chapter10.Exercise32.core_normal_multiple`, `Rudin.Chapter10.Exercise32.boundary_decomposition`, `Rudin.Chapter10.Exercise32.triangulated_boundary`, `Rudin.Chapter10.Exercise32.corner_images`, `Rudin.Chapter10.Exercise32.edge_endpoints`, `Rudin.Chapter10.Exercise32.first_edge_winding`, `Rudin.Chapter10.Exercise32.edge1_projection`, `Rudin.Chapter10.Exercise32.third_edge_winding`, `Rudin.Chapter10.Exercise32.edge3_full`, `Rudin.Chapter10.Exercise32.repeated_seam_maps`, `Rudin.Chapter10.Exercise32.boundary_repeated_seam`, `Rudin.Chapter10.Exercise32.geometricEdge_closed`, `Rudin.Chapter10.Exercise32.geometricEdge_first_half`, `Rudin.Chapter10.Exercise32.geometricEdge_second_half`, `Rudin.Chapter10.Exercise32.geometric_edge_range`, `Rudin.Chapter10.Exercise32.rim_subset_band`, `Rudin.Chapter10.Exercise32.parametrized_boundary_integral`, `Rudin.Chapter10.Exercise32.boundary_source_integrals`, `Rudin.Chapter10.Exercise32.edge1_integral`, `Rudin.Chapter10.Exercise32.edge3_integral`, `Rudin.Chapter10.Exercise32.geometric_edge_integral`, `Rudin.Chapter10.Exercise32.geometric_edge_chain_integral`, `Rudin.Chapter10.Exercise32.geometric_edge_source_integral`, `Rudin.Chapter10.Exercise32.geometric_edge_ne_parameter_boundary`.

<a id="chapter-11"></a>

## Chapter 11 — The Lebesgue Theory

**Exercises:** [1](#r11e01) · [2](#r11e02) · [3](#r11e03) · [4](#r11e04) · [5](#r11e05) · [6](#r11e06) · [7](#r11e07) · [8](#r11e08) · [9](#r11e09) · [10](#r11e10) · [11](#r11e11) · [12](#r11e12) · [13](#r11e13) · [14](#r11e14) · [15](#r11e15) · [16](#r11e16) · [17](#r11e17) · [18](#r11e18)

<a id="r11e01"></a>
### 11.1 — Zero nonnegative integral implies zero almost everywhere
**Lean source:** [Exercise01.lean](../../Math/Rudin/Chapter11/Exercise01.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $(X,\mu)$ be a measure space, $E\subseteq X$ measurable, and $f$ a real function that is measurable on $E$ and satisfies $f\ge0$ there. If its nonnegative Lebesgue integral satisfies

$$
\int_E f\,d\mu=0,
$$

then $f=0$ almost everywhere on $E$; equivalently, $\mu(\{x\in E:f(x)\ne0\})=0$. No assumption that $\mu(E)$ is finite is needed. The formal statements permit measurability almost everywhere for the restricted measure and also cover functions valued in $[0,\infty]$.

**Proof.** For each positive integer $n$, put

$$
E_n=\{x\in E:f(x)\ge1/n\}.
$$

Monotonicity of the nonnegative integral gives

$$
0=\int_E f\,d\mu\ge\frac1n\mu(E_n).
$$

Hence every $E_n$ has measure zero. Since $f\ge0$ on $E$, its nonzero set there is $\bigcup_{n\ge1}E_n$, which also has measure zero. This argument includes the value $+\infty$. For a function measurable only almost everywhere, take a measurable representative for the restricted measure; the null exceptional set does not change the conclusion. The Lean proof applies the standard zero-nonnegative-integral criterion directly.

**Scope.** For real-valued $f$, the file uses the nonnegative integral after embedding the nonnegative values into $[0,\infty]$. Nonnegativity on $E$ ensures that this loses no values. A separate Bochner-integral version assumes explicitly that $f$ is integrable on $E$. For a nonnegative integrable function this integral agrees with the nonnegative integral, so the same conclusion follows. The integrability assumption is necessary for that formulation because Lean assigns the Bochner integral the default value zero for nonintegrable functions; that default is not the source's zero-integral hypothesis.

**Lean declarations:** `exercise01`, `exercise01_ennreal`, `exercise01_integrable`.

<a id="r11e02"></a>
### 11.2 — Vanishing integrals on measurable subsets
**Lean source:** [Exercise02.lean](../../Math/Rudin/Chapter11/Exercise02.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $E$ be measurable in a measure space $(X,\mu)$, and let $f$ be integrable on $E$. If $\int_A f\,d\mu=0$ for every measurable $A\subseteq E$, then $f=0$ almost everywhere on $E$. The result holds for real and complex functions, and for functions with values in a complete real normed space. The measure need not be finite or sigma-finite.

**Proof.** Apply the standard uniqueness criterion for an integrable function from its integrals over measurable sets, using the restricted measure $\mu|_E$. For every measurable $A\subseteq X$, restriction of the set integral gives

$$
\int_A f\,d(\mu|_E)=\int_{A\cap E}f\,d\mu=0.
$$

The criterion gives $f=0$ almost everywhere for $\mu|_E$. Since $E$ is measurable, this is exactly $f=0$ almost everywhere on $E$ for $\mu$. The explicit integrability hypothesis excludes the default value assigned to a nonintegrable Bochner integral.

**Lean declarations:** `Rudin.Chapter11.exercise02`.

<a id="r11e03"></a>
### 11.3 — Measurability of the convergence set
**Lean source:** [Exercise03.lean](../../Math/Rudin/Chapter11/Exercise03.lean).
**Inventory status:** Verified as stated.

**Statement.** For measurable real functions $f_n$ on a measurable space $X$, the set of $x$ for which $f_n(x)$ has a finite real limit is measurable. The same assertion holds for complex functions and finite complex limits.

**Proof.** The standard measurable convergence-set theorem applies to real-valued measurable functions. Its countable Cauchy criterion can be written as

$$
\bigcap_{j\ge1}\ \bigcup_{N\ge0}\ \bigcap_{m,n\ge N}
\{x:|f_m(x)-f_n(x)|<1/j\}.
$$

Each set in this expression is measurable, and completeness of $\mathbb R$ identifies the Cauchy condition with convergence to a real number. This excludes divergence to either infinity.

A complex sequence converges if and only if its real and imaginary parts both converge to finite real limits. Necessity follows from continuity of the coordinate maps. Conversely, limits $a,b$ of the coordinates give the limit $a+ib$ by addition and multiplication by $i$. The complex convergence set is therefore the intersection of the two measurable real convergence sets.

**Lean declarations:** `Rudin.Chapter11.exercise03_real`, `Rudin.Chapter11.exercise03_complex_iff`, `Rudin.Chapter11.exercise03_complex`.

<a id="r11e04"></a>
### 11.4 — A bounded measurable multiplier
**Lean source:** [Exercise04.lean](../../Math/Rudin/Chapter11/Exercise04.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $E$ be measurable, $f$ integrable on $E$, and $g$ measurable and bounded on $E$. Then $fg$ is integrable on $E$, for real or complex functions. More generally, the integrability result needs only almost-everywhere strong measurability of $g$ for $\mu|_E$, together with a pointwise bound $\|g(x)\|\le C$ on $E$. Separate results establish ordinary measurability of the product on the subtype $E$ when both factors are measurable there.

**Proof.** Multiplication is continuous over either scalar field, so the product of two measurable functions on $E$ is measurable. For the almost-everywhere formulation, multiply almost-everywhere strongly measurable representatives. On $E$,

$$
\|f(x)g(x)\|\le C\|f(x)\|.
$$

The bounded-multiplier integrability theorem, applied to the restricted measure, now gives integrability and almost-everywhere strong measurability of the product. If $E$ is empty, both conclusions hold without a sign condition on the chosen bound.

**Lean declarations:** `Rudin.Chapter11.exercise04`, `Rudin.Chapter11.exercise04_measurable_real`, `Rudin.Chapter11.exercise04_measurable_complex`.

<a id="r11e05"></a>
### 11.5 — Strict inequality in Fatou's lemma
**Lean source:** [Exercise05.lean](../../Math/Rudin/Chapter11/Exercise05.lean).
**Inventory status:** Verified as stated.

**Statement.** On $[0,1]$, let $g$ be zero on $[0,1/2]$ and one on $(1/2,1]$. Set $f_{2k}(x)=g(x)$ and $f_{2k+1}(x)=g(1-x)$. Then $0\le f_n\le1$, each $f_n$ is integrable, and

$$
\liminf_{n\to\infty}f_n(x)=0\quad(x\in[0,1]),
\qquad \int_{[0,1]}f_n(x)\,dx=\frac12.
$$

**Proof.** Extend $g$ to the real line as the indicator of $(1/2,1]$. Reflection gives $g(1-x)=\mathbf1_{[0,1/2)}(x)$. Thus both parities take only the values zero and one. If $x\le1/2$, all even terms vanish. If $x>1/2$, all odd terms vanish. There are arbitrarily large indices of either parity, so nonnegativity and these zero subsequences give the stated lower limit. At $x=1/2$ every term is zero; at $0$ and $1$ the values alternate between zero and one. This includes all boundary cases of the closed interval.

Both indicator sets are measurable and have length $1/2$, so their indicators are integrable and have integral $1/2$. Hence the integral of the pointwise lower limit is zero, whereas the lower limit of the integrals is $1/2$.

**Lean declarations:** `Rudin.Chapter11.exercise05_even`, `Rudin.Chapter11.exercise05_odd`, `Rudin.Chapter11.exercise05_reflection`, `Rudin.Chapter11.exercise05_bounds`, `Rudin.Chapter11.exercise05_lower_limit`, `Rudin.Chapter11.exercise05_integrable`, `Rudin.Chapter11.exercise05_integrals`.

<a id="r11e06"></a>
### 11.6 — Uniform convergence on infinite and finite measure spaces
**Lean source:** [Exercise06.lean](../../Math/Rudin/Chapter11/Exercise06.lean).
**Inventory status:** Verified as stated.

**Statement.** For $n\ge1$, define $f_n(x)=1/n$ when $|x|\le n$, and $f_n(x)=0$ otherwise. These functions converge uniformly to zero on $\mathbb R$, but every integral equals $2$. There is no integrable function $g$ with $|f_n|\le g$ almost everywhere for every $n\ge1$.

In contrast, let $E$ be a measurable set of finite measure. Suppose $F_n:E\to V$ are almost-everywhere strongly measurable, each is bounded, and $F_n\to f$ uniformly on $E$. For a complete real normed space $V$, this includes real and complex values. Then a single nonnegative constant bounds every $F_n$ and $f$ on $E$. This constant is integrable on $E$, all these functions are integrable there, and

$$
\lim_{n\to\infty}\int_E F_n\,d\mu=\int_E f\,d\mu.
$$

**Proof.** The estimate $\|f_n(x)\|\le1/n$ proves uniform convergence. The indicator of $[-n,n]$ times $1/n$ is integrable, and its integral is $(2n)/n=2$ for $n\ge1$. The formal sequence also has an auxiliary index $n=0$; its value is zero, and the integral formula is asserted only for positive indices. If an integrable common majorant existed, dominated convergence applied to $f_{n+1}$ would make its integrals tend to zero. Their constant value $2$ gives a contradiction.

For the finite-measure assertion, write $\|F_n(x)\|\le C_n$. Choose $N$ so that $\|F_n(x)-f(x)\|<1$ on $E$ for $n\ge N$. First $\|f(x)\|\le|C_N|+1$, and then $\|F_n(x)\|\le|C_N|+2$ for all $n\ge N$. The finitely many earlier bounds can be included by taking

$$
B=\sum_{i=0}^{N}|C_i|+2.
$$

Thus $B\ge0$ bounds the entire sequence and its limit. This common-bound argument itself needs neither measurability nor finite measure. Finite measure makes the constant function $B$ integrable on $E$. Pointwise convergence on $E$ gives almost-everywhere strong measurability of $f$ from that of the terms. Domination proves integrability of all terms and the limit, and the dominated convergence theorem gives the integral limit. Zero measure and the empty set require no separate exclusion.

**Lean declarations:** `Rudin.Chapter11.exercise06_literal`, `Rudin.Chapter11.exercise06_bound`, `Rudin.Chapter11.exercise06_uniform_limit`, `Rudin.Chapter11.exercise06_integrable`, `Rudin.Chapter11.exercise06_integrals`, `Rudin.Chapter11.exercise06_no_domination`, `Rudin.Chapter11.exercise06_common_bound`, `Rudin.Chapter11.exercise06_finite_measure_domination`, `Rudin.Chapter11.exercise06_finite_measure_convergence`.

<a id="r11e07"></a>
### 11.7 — A criterion for raw Riemann–Stieltjes integrability
**Lean source:** [Exercise07.lean](../../Math/Rudin/Chapter11/Exercise07.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $a\le b$, let $f:\mathbb R\to\mathbb R$, and let $\alpha:\mathbb R\to\mathbb R$ be nondecreasing on $[a,b]$. No continuity of $\alpha$ is assumed. For a weak partition $P=(a=x_0\le\cdots\le x_m=b)$, put

$$
\omega_i(f,P)=\sup_{[x_i,x_{i+1}]}f-\inf_{[x_i,x_{i+1}]}f,
\qquad
W_P(y)=\sum_{i=0}^{m-1}\omega_i(f,P)
\mathbf1_{(\alpha(x_i),\alpha(x_{i+1})]}(y).
$$

Then $f$ has a Riemann–Stieltjes integral with the actual values of $\alpha$ if and only if $f$ is bounded on $[a,b]$ and there is a sequence of weak partitions $P_n$ such that $W_{P_n}(y)\to0$ for Lebesgue-almost every mass coordinate $y$. This criterion is proved for both the Darboux definition and the equivalent definition that controls every tagged refinement of a partition. No measurability assumption on $f$ is imposed.

The criterion also implies the necessary one-sided conditions: a positive left jump of $\alpha$ at $c\in(a,b]$ requires left continuity of $f$ at $c$, and a positive right jump at $c\in[a,b)$ requires right continuity. At the two endpoints, only the inward condition applies. At an interior point with both jump parts positive, $f$ must be continuous relative to $[a,b]$. One can include these conditions explicitly in the equivalence; they already follow from boundedness and almost-everywhere vanishing of $W_{P_n}$.

**Proof.** If $|f|\le M$ on $[a,b]$, each closed-cell oscillation lies between zero and $2M$. The half-open mass intervals are disjoint apart from empty cells. Thus $W_P$ is integrable and

$$
0\le W_P\le2M\mathbf1_{(\alpha(a),\alpha(b)]},
\qquad
\int_{\mathbb R}W_P(y)\,dy=U(P,f,\alpha)-L(P,f,\alpha).
$$

The equality follows by integrating each indicator; its length is the raw increment $\alpha(x_{i+1})-\alpha(x_i)$. If an integral exists, choose partitions whose Darboux gaps are less than $1/(n+1)$. The nonnegative functions $W_{P_n}$ tend to zero in $L^1$. The standard subsequence theorem for convergence in measure gives a subsequence tending to zero almost everywhere. Conversely, if such a sequence tends to zero almost everywhere, the displayed integrable bound and dominated convergence make its Darboux gaps tend to zero. Arbitrarily small gaps give existence of the Darboux integral. The proved equivalence of the Darboux and tagged-refinement definitions gives the second formulation.

For the left jump condition, the precise local assumption is that some $d>0$ satisfies $d\le\alpha(c)-\alpha(t)$ for every $t\in[a,c)$. Any partition has a closed cell containing $c$ with left endpoint less than $c$. Its mass is at least $d$, and its oscillation times its mass is at most the full Darboux gap. A gap smaller than $d\varepsilon$ therefore gives oscillation less than $\varepsilon$ on a left neighborhood of $c$, including its value at $c$. This is left continuity. The right-side argument uses a cell whose right endpoint is greater than $c$ and the condition $d\le\alpha(t)-\alpha(c)$ for $t\in(c,b]$. Combining the two sides proves relative continuity when both jumps are positive. For globally nondecreasing $\alpha$, these assumptions follow respectively from $\alpha(c-)<\alpha(c)$ and $\alpha(c)<\alpha(c+)$.

To compare with the source's measure hint, suppose now that $\alpha$ is globally nondecreasing. Its source measure $\mu_\alpha$, formed from the right-limit normalization, has the following interval values for $u<v$:

$$
\begin{aligned}
\mu_\alpha((u,v))&=\alpha(v-)-\alpha(u+),\\
\mu_\alpha((u,v])&=\alpha(v+)-\alpha(u+),\\
\mu_\alpha([u,v))&=\alpha(v-)-\alpha(u-),\\
\mu_\alpha([u,v])&=\alpha(v+)-\alpha(u-),\\
\mu_\alpha(\{c\})&=(\alpha(c)-\alpha(c-))+(\alpha(c+)-\alpha(c)).
\end{aligned}
$$

The formal formulas use the nonnegative part when endpoints are not ordered. In particular, the raw mass of a nonempty cell is

$$
\alpha(v)-\alpha(u)=\mu_\alpha((u,v))
 +(\alpha(u+)-\alpha(u))+(\alpha(v)-\alpha(v-)).
$$

The two endpoint terms retain the split of each atom at the actual value of $\alpha$. Dropping them changes the criterion. Repeated nodes give empty mass intervals and contribute nothing. On a singleton interval every $W_P$ is zero and every real $f,\alpha$ has both integrals equal to zero. More generally, if $\alpha(a)=\alpha(b)$, integrability is equivalent to boundedness and the integral is zero; no continuity is needed.

For $\alpha(x)=x$, the criterion is precisely boundedness and continuity almost everywhere on $[a,b]$. To see necessity, discard the countable union of all partition nodes and the null set where $W_{P_n}$ fails to vanish. At a remaining point $x$, choose a partition whose oscillation at $x$ is small. The point is in the interior of one cell, so that small oscillation bounds $|f(z)-f(x)|$ for all sufficiently close $z$. This proves relative continuity almost everywhere. Conversely, on uniform grids the closed-cell oscillations tend to zero at every relative continuity point. Dominated convergence gives small Darboux gaps, and hence integrability. This includes $a=b$.

The file also proves concrete tests of the jump and endpoint conventions. Let $D(x)=\mathbf1_{(0,\infty)}(x)$ and $H(x)=\mathbf1_{[0,\infty)}(x)$. On $[-1,1]$, $D$ is integrable with respect to $H$ with integral zero: on $[-1,0]$ the integrand is zero, and on $[0,1]$ the integrator is constant. Yet $\mu_H(\{0\})=1$ and $D$ is discontinuous at zero. Thus continuity $\mu_\alpha$-almost everywhere is not necessary. In contrast, $D$ is not integrable with respect to $D$ on $[0,1]$ or $[-1,1]$, and $H$ is not integrable with respect to $H$ on $[-1,0]$. The corresponding inward jump conditions would require the false right or left continuity at zero. Moreover $D$ and $H$ give exactly the same source measure, so a change only in the raw value at a jump can change integrability without changing that measure. Even for the constant integrand $1$ on $[-1,0]$, the raw integral with respect to $D$ is zero while its normalized measure integral is one. These are limitations of the naive measure substitution, not limitations of the criterion above.

**Lean declarations:** `Rudin.Chapter11.Exercise07.exercise07`, `Rudin.Chapter11.Exercise07.exercise07_tagged`, `Rudin.Chapter11.Exercise07.exercise07_with_one_sided_conditions`, `Rudin.Chapter11.Exercise07.exercise07_id`, `Rudin.Chapter11.Exercise07.vanishingMassOscillation_of_integral`, `Rudin.Chapter11.Exercise07.integral_of_vanishingMassOscillation`, `Rudin.Chapter11.Exercise07.integral_massOscillation`, `Rudin.Chapter11.Exercise07.cellOscillation_bounds`, `Rudin.Chapter11.Exercise07.massOscillation_bounds`, `Rudin.Chapter11.Exercise07.integrable_massOscillation`, `Rudin.Chapter11.Exercise07.ae_continuous_of_vanishing_id`, `Rudin.Chapter11.Exercise07.left_continuous_of_positive_jump`, `Rudin.Chapter11.Exercise07.right_continuous_of_positive_jump`, `Rudin.Chapter11.Exercise07.continuous_of_two_positive_jumps`, `Rudin.Chapter11.Exercise07.left_continuous_of_leftLim_lt`, `Rudin.Chapter11.Exercise07.right_continuous_of_lt_rightLim`, `Rudin.Chapter11.Exercise07.sourceMeasure_Ioo`, `Rudin.Chapter11.Exercise07.sourceMeasure_Ioc`, `Rudin.Chapter11.Exercise07.sourceMeasure_Ico`, `Rudin.Chapter11.Exercise07.sourceMeasure_Icc`, `Rudin.Chapter11.Exercise07.sourceMeasure_atom`, `Rudin.Chapter11.Exercise07.raw_increment_sourceMeasure`, `Rudin.Chapter11.Exercise07.repeated_node_mass`, `Rudin.Chapter11.Exercise07.massOscillation_self`, `Rudin.Chapter11.Exercise07.exercise07_self`, `Rudin.Chapter11.Exercise07.exercise07_zero_mass`, `Rudin.Chapter11.Exercise07.exercise07_normalization_endpoint`, `Rudin.Chapter11.Exercise07.monotone_immediateStep`, `Rudin.Chapter11.Exercise07.opposite_jump_integrable`, `Rudin.Chapter11.Exercise07.shared_right_endpoint_jump_not_integrable`, `Rudin.Chapter11.Exercise07.shared_left_endpoint_jump_not_integrable`, `Rudin.Chapter11.Exercise07.shared_right_interior_jump_not_integrable`, `Rudin.Chapter11.Exercise07.positive_atom_discontinuous_integrable`, `Rudin.Chapter11.Exercise07.source_ae_continuity_not_necessary`, `Rudin.Chapter11.Exercise07.raw_value_changes_integrability`.

<a id="r11e08"></a>
### 11.8 — The derivative of a Riemann primitive almost everywhere
**Lean source:** [Exercise08.lean](../../Math/Rudin/Chapter11/Exercise08.lean).
**Inventory status:** Verified as stated.

**Statement.** Suppose $a\le b$ and $f$ has an ordinary Riemann integral on $[a,b]$. For every $x\in[a,b]$ the Riemann integral defining $F(x)=\int_a^x f(t)\,dt$ exists, including at the endpoints. Moreover $F$ has a genuine derivative $F'(x)=f(x)$ for Lebesgue-almost every $x\in[a,b]$. Both the Darboux and tagged-refinement hypotheses are covered.

**Proof.** Split the given Darboux integral at $x$. The ordinary Riemann-to-Lebesgue bridge proves interval integrability and equality of the two integral values on $[a,x]$, without adding a measurability assumption. Thus the displayed Lebesgue primitive is the actual Riemann primitive at each point of the closed interval. Apply the standard almost-everywhere differentiation theorem for the indefinite Lebesgue integral to the interval-integrable function. It gives existence of the derivative and its value $f(x)$ almost everywhere on $[a,b]$, not merely an assigned value for a derivative operator. Endpoints are null and require no imposed derivative convention. For $a=b$ the almost-everywhere assertion is vacuous and the primitive integral is zero. The tagged version follows from its proved equivalence with Darboux integrability.

**Lean declarations:** `Rudin.Chapter11.exercise08_riemann_primitive`, `Rudin.Chapter11.exercise08_almost_everywhere_derivative`, `Rudin.Chapter11.exercise08_tagged_almost_everywhere_derivative`.

<a id="r11e09"></a>
### 11.9 — Continuity of an indefinite Lebesgue integral
**Lean source:** [Exercise09.lean](../../Math/Rudin/Chapter11/Exercise09.lean).
**Inventory status:** Verified as stated.

**Statement.** If $a\le b$ and $f$ is Lebesgue integrable on $[a,b]$, then $F(x)=\int_a^x f(t)\,dt$ is continuous on the entire closed interval. This includes both endpoints and holds for functions with values in any complete real normed space, including $\mathbb R$ and $\mathbb C$. Riemann integrability is not assumed.

**Proof.** Apply the standard continuity theorem for an interval-integral primitive to the integrable function on the unordered closed interval, which equals $[a,b]$ because $a\le b$. The theorem follows from dominated convergence for moving interval indicators: as $x$ tends to $x_0$ within $[a,b]$, the indicators converge away from the single point $x_0$, and the norms of the integrands are bounded by the integrable function $\|f\|$. This also proves the one-sided continuity required at each endpoint. On a singleton interval the primitive is zero.

**Lean declarations:** `Rudin.Chapter11.exercise09_continuity`.

<a id="r11e10"></a>
### 11.10 — The finite-measure inclusion and an infinite-measure counterexample
**Lean source:** [Exercise10.lean](../../Math/Rudin/Chapter11/Exercise10.lean).
**Inventory status:** Verified as stated.

**Statement.** On a finite measure space, every $L^2$ function is integrable. This includes zero measure and normed-group-valued functions under the usual almost-everywhere strong measurability convention. On $\mathbb R$ with Lebesgue measure,

$$
f(x)=\frac1{1+|x|}
$$

is continuous and belongs to $L^2$, but is not integrable. The total measure of this space is infinite.

**Proof.** The standard comparison of $L^p$ exponents on finite measure spaces gives $L^2\subseteq L^1$, and membership in $L^1$ is equivalent to integrability. It does not require positive total measure. For the example, continuity follows from positivity of $1+|x|$. The standard integrability theorem for $(1+\|x\|)^{-r}$ in dimension one, with $r=2>1$, proves integrability of $f^2$ and hence $L^2$ membership.

If $f$ were integrable, then $2f$ would be integrable. For $x>1$,

$$
\frac1x\le\frac2{1+x}=2f(x).
$$

Domination would make $x^{-1}$ integrable on $(1,\infty)$. The power-integral criterion says $x^r$ is integrable there only for $r<-1$, contradicting $r=-1$. Thus infinite measure does not permit the unrestricted inclusion.

**Lean declarations:** `Rudin.Chapter11.exercise10_finite_measure_inclusion`, `Rudin.Chapter11.exercise10_continuous`, `Rudin.Chapter11.exercise10_square_integrable`, `Rudin.Chapter11.exercise10_memLp_two`, `Rudin.Chapter11.exercise10_nonintegrable`, `Rudin.Chapter11.exercise10_infinite_measure`.

<a id="r11e11"></a>
### 11.11 — The complete metric space of integrable function classes
**Lean source:** [Exercise11.lean](../../Math/Rudin/Chapter11/Exercise11.lean).
**Inventory status:** Verified as stated.

**Statement.** Identify integrable functions that agree almost everywhere. On these $L^1(\mu)$ classes,

$$
d(f,g)=\int_X\|f(x)-g(x)\|\,d\mu
$$

is a complete metric when the values lie in a complete real normed space, including real and complex scalars. No finiteness assumption on $\mu$ is required. On actual functions the same formula is only a pseudometric, as the chapter's almost-everywhere quotient convention requires.

**Proof.** The difference of two integrable representatives is integrable, and so is its norm. If either representative is replaced by an almost-everywhere equal function, the integrand changes only on a null set, so its integral is unchanged. The $L^1$ distance formula identifies this integral exactly with the norm distance on the library's quotient space at exponent one. Thus nonnegativity, symmetry, and the triangle inequality follow from the norm metric, and distance zero means equality of classes. For raw integrable functions it means exactly equality almost everywhere. Mapping each raw function to its $L^1$ class preserves the displayed distance.

The standard completeness theorem for $L^p$, at $p=1$ and for complete target space, supplies completeness of this metric. Consequently a Cauchy sequence of classes has a class $f\in L^1$ such that

$$
\int_X\|f_n(x)-f(x)\|\,d\mu\longrightarrow0.
$$

Finally, on $[0,1]$ with Lebesgue measure take the actual functions $f=\mathbf1_{\{0\}}$ and $g=0$. Both are integrable and agree almost everywhere, but $f(0)=1\ne0=g(0)$. Their distance is zero. This proves the failure of pointwise separation without the quotient; it is not a refutation of the source under its stated convention.

**Lean declarations:** `Rudin.Chapter11.exercise11_distance`, `Rudin.Chapter11.exercise11_norm_difference`, `Rudin.Chapter11.exercise11_distance_integrable`, `Rudin.Chapter11.exercise11_metric_axioms`, `Rudin.Chapter11.exercise11_representative_independence`, `Rudin.Chapter11.exercise11_toL1_distance`, `Rudin.Chapter11.exercise11_zero_iff_ae`, `Rudin.Chapter11.exercise11_complete`, `Rudin.Chapter11.exercise11_cauchy_converges`, `Rudin.Chapter11.exercise11_raw_function_degeneracy`.

<a id="r11e12"></a>
### 11.12 — Integrating a separately continuous function
**Lean source:** [Exercise12.lean](../../Math/Rudin/Chapter11/Exercise12.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $f:[0,1]^2\to\mathbb R$ or $\mathbb C$ be separately continuous and satisfy $\|f(x,y)\|\le1$. Then

$$
g(x)=\int_0^1 f(x,y)\,dy
$$

is continuous on the closed interval $[0,1]$, including its endpoints. Every section integral exists. The continuity result also holds with values in any complete real normed space. Joint continuity and joint measurability are not assumed. Separate results identify the real and complex section integrals as actual Riemann integrals, not just totalized Lebesgue values.

**Proof.** For each fixed $x$, continuity of $y\mapsto f(x,y)$ on a compact interval proves its interval integrability and supplies its measurability. At a fixed $x_0\in[0,1]$, continuity of $x\mapsto f(x,y)$ for each $y$ gives convergence of the sections as $x\to x_0$ within $[0,1]$. Their norms are bounded by the integrable constant $1$. The parameter form of dominated convergence therefore proves continuity of $g$ relative to $[0,1]$, so the same argument covers one-sided endpoint limits.

For real sections, boundedness and continuity imply the closed-cell Darboux Riemann criterion and equality with the Lebesgue interval integral. For complex sections, apply the real result to real and imaginary parts; each is bounded by the complex norm. The proved equivalence between complex tagged sums and their two real components then gives the complex Riemann integral, with the same value because integration commutes with the two coordinates.

**Lean declarations:** `Rudin.Chapter11.exercise12_section_integrable`, `Rudin.Chapter11.exercise12_continuity`, `Rudin.Chapter11.exercise12_real_riemann`, `Rudin.Chapter11.exercise12_complex_riemann`.

<a id="r11e13"></a>
### 11.13 — A closed bounded noncompact set in L²
**Lean source:** [Exercise13.lean](../../Math/Rudin/Chapter11/Exercise13.lean).
**Inventory status:** Verified as stated.

**Statement.** In real $L^2([-\pi,\pi])$ with Lebesgue measure and equality almost everywhere, let $s_n$ be the class of $x\mapsto\sin(nx)$, $n\ge1$. The set $\{s_n:n\ge1\}$ is closed and bounded but not compact. More precisely,

$$
\|s_n\|^2=\pi,\qquad d(s_n,s_m)=\sqrt{2\pi}\quad(n\ne m).
$$

The file also proves that the normalized sine classes are orthonormal and that the sine coefficients of every fixed $L^2$ vector tend to zero. In particular, for every Lebesgue-measurable $E\subseteq[-\pi,\pi]$,

$$
\int_E\sin(nx)\,dx\longrightarrow0\quad(n\to\infty).
$$

**Proof.** The literal sine functions are measurable and bounded by one on a finite-measure interval, so they define $L^2$ classes. The integral of $\cos(kx)$ on $[-\pi,\pi]$ is zero for every nonzero integer $k$. The identity

$$
\sin(nx)\sin(mx)=\frac{\cos((n-m)x)-\cos((n+m)x)}2
$$

therefore gives inner product $\pi$ when $n=m$ and zero otherwise. The diagonal identity gives norm $\sqrt\pi$; expanding the squared norm of a difference gives squared distance $2\pi$ for distinct indices. The classes are represented by the displayed literal functions almost everywhere, so these are their actual $L^2$ distances.

A sequence with pairwise distances at least the positive constant $\sqrt{2\pi}$ is a closed embedding of the discrete index space. Its range is closed, and its constant norm makes it bounded. If the range were compact, this embedding would make the infinite discrete space of natural-number indices compact. A compact discrete space is finite, which is a contradiction.

Dividing the sine classes by $\sqrt\pi$ gives an orthonormal family. Bessel's inequality makes the squared inner products with any fixed vector summable, so the coefficients tend to zero. The indicator of any Lebesgue-measurable subset $E$ belongs to this $L^2$ space. Its inner products with the sine classes are exactly the displayed set integrals, proving their limit. The formal indicator results use null measurability, so they do not restrict $E$ to Borel sets. The formal indices are $n+1$ with $n\in\mathbb N$.

**Lean declarations:** `Rudin.Chapter11.exercise13_closedness`, `Rudin.Chapter11.exercise13_boundedness`, `Rudin.Chapter11.exercise13_noncompactness`, `Rudin.Chapter11.SineL2.memLp_sin`, `Rudin.Chapter11.SineL2.sine_ae`, `Rudin.Chapter11.SineL2.integral_cos_int`, `Rudin.Chapter11.SineL2.integral_sine_mul`, `Rudin.Chapter11.SineL2.inner_sine`, `Rudin.Chapter11.SineL2.norm_sine_sq`, `Rudin.Chapter11.SineL2.norm_sine`, `Rudin.Chapter11.SineL2.dist_sine`, `Rudin.Chapter11.SineL2.closedEmbedding_sine`, `Rudin.Chapter11.SineL2.orthonormal_normalized`, `Rudin.Chapter11.SineL2.tendsto_inner_sine`, `Rudin.Chapter11.SineL2.memLp_indicator`, `Rudin.Chapter11.SineL2.inner_sine_indicator`, `Rudin.Chapter11.SineL2.tendsto_setIntegral_sine`.

<a id="r11e14"></a>
### 11.14 — Complex measurability and open preimages
**Lean source:** [Exercise14.lean](../../Math/Rudin/Chapter11/Exercise14.lean).
**Inventory status:** Verified as stated.

**Statement.** For a function $f:X\to\mathbb C$ on a measurable space, measurability of both $\operatorname{Re}f$ and $\operatorname{Im}f$ is equivalent to measurability of $f^{-1}(V)$ for every open $V\subseteq\mathbb C$.

**Proof.** The standard coordinate characterization of the Borel measurable structure on $\mathbb C$ says that measurable real and imaginary parts make $f$ measurable. The preimage of any open set is then measurable, since open sets are Borel. Conversely, the Borel sigma-algebra is generated by open sets. Measurable preimages of all open sets therefore imply measurability of $f$. Composing it with the continuous real and imaginary coordinate maps gives both coordinate measurability assertions. Combining these directions gives the equivalence.

**Lean declarations:** `Rudin.Chapter11.exercise14_open_preimages`, `Rudin.Chapter11.exercise14_coordinate_measurability`, `Rudin.Chapter11.exercise14`.

<a id="r11e15"></a>
### 11.15 — An additive elementary charge with no countably additive extension
**Lean source:** [Exercise15.lean](../../Math/Rudin/Chapter11/Exercise15.lean).
**Inventory status:** Verified as stated.

**Statement.** On the ring of elementary subsets of $(0,1]$, the following prescriptions determine a well-defined, finite, nonnegative, finitely additive real set function $\phi$. Each of $[a,b]$, $[a,b)$, $(a,b]$, and $(a,b)$ has value $b-a$ when $0<a\le b\le1$. Both $(0,b)$ and $(0,b]$ have value $1+b$ when $0<b\le1$. Empty intervals and all singletons in $(0,1]$ have value zero. The charge is not regular in the sense of ambient-real closed inner sets and open outer sets. It has no countably additive extension to any sigma-ring containing the elementary ring, even if signed extended-real values are permitted.

**Proof.** An elementary set is a finite union of order-connected subsets of $(0,1]$. Each such subset is one of the four interval types, including empty intervals and singletons. Intersections remain intervals, and the difference of two intervals splits into at most two disjoint intervals. Thus the finite unions form a ring, and every elementary set has a finite disjoint interval decomposition.

Say that $A$ contains the right germ at zero if it contains every sufficiently small positive number. For an interval in $(0,1]$, either it or its complement contains this germ. To prove this, if the interval has points arbitrarily close to zero, fix any one of its positive points and use order-connectedness between that point and smaller points. This gives a whole right neighborhood of zero inside the interval. Otherwise some right neighborhood misses the interval. Finite unions preserve this dichotomy. Hence the literal indicator of every elementary set is eventually constant, with value zero or one, as $x\downarrow0$.

Define canonically on sets

$$
\phi(A)=m(A)+\mathbf1_{\{A\text{ contains the right germ at }0\}}.
$$

Every elementary set is measurable and contained in $(0,1]$, so this value is finite. Intervals bounded away from zero have no germ and have their usual length, including the degenerate cases. The two intervals starting at zero contain the germ and have value $1+b$. For disjoint elementary sets, both cannot contain the germ, and their union contains it exactly when one does. Thus the germ term is additive on disjoint pairs, as is length. Induction gives finite additivity for every finite disjoint family. The sum over any disjoint interval decomposition equals this canonical set value, so different decompositions give the same sum. The file proves these statements both for a finite nonnegative extended-value encoding and for the real charge, with a proved comparison between them.

For nonregularity, take $A=(0,1/2)$, whose charge is $3/2$. Every ambient-real closed $F\subseteq(0,1]$ is compact and bounded away from zero: the open complement of $F$ contains a neighborhood of zero. Therefore a closed elementary $F\subseteq A$ has no germ and $\phi(F)=m(F)\le1/2$. The inner regularity inequality with $\varepsilon=1/2$ would give $3/2\le\phi(F)+1/2\le1$, a contradiction. The same witness disproves the weaker variant with relative openness of outer sets at the endpoint $1$; the inner sets must still be closed in $\mathbb R$. Relative closedness of the inner sets would be a different condition.

Finally, the elementary intervals

$$
D_n=(2^{-(n+1)},2^{-n}],\qquad n\ge0,
$$

are pairwise disjoint and have union $(0,1]$. Each is bounded away from zero, so its charge equals its length. Consequently

$$
\sum_{n=0}^{\infty}\phi(D_n)=1,
\qquad \phi\!\left(\bigcup_{n=0}^{\infty}D_n\right)=\phi((0,1])=2.
$$

Any countably additive extension agreeing on the elementary sets would contradict these equalities. This argument needs only that the extension's domain contain the elementary ring, not additional topology. For a signed extended-real extension, its ordered partial sums on this same family are finite real sums tending to $1$, while countable additivity would make them tend to the union's value $2$. Uniqueness of limits gives the same contradiction. Thus the obstruction covers the source's signed extension convention as well as nonnegative measures.

**Lean declarations:** `Rudin.Chapter11.ElementaryCharge.elementary_ring`, `Rudin.Chapter11.ElementaryCharge.intervals_semiring`, `Rudin.Chapter11.ElementaryCharge.intervals_eq_fourIntervals`, `Rudin.Chapter11.ElementaryCharge.elementary_eq_fourIntervals`, `Rudin.Chapter11.ElementaryCharge.disjoint_decomposition`, `Rudin.Chapter11.ElementaryCharge.elementary_iff_finite_disjoint`, `Rudin.Chapter11.ElementaryCharge.interval_germ_constant`, `Rudin.Chapter11.ElementaryCharge.germ_union_constant`, `Rudin.Chapter11.ElementaryCharge.germ_constant`, `Rudin.Chapter11.ElementaryCharge.indicator_germ_constant`, `Rudin.Chapter11.ElementaryCharge.eventual_membership`, `Rudin.Chapter11.ElementaryCharge.subset_domain`, `Rudin.Chapter11.ElementaryCharge.measurable`, `Rudin.Chapter11.ElementaryCharge.finite_value`, `Rudin.Chapter11.ElementaryCharge.germ_not_compl`, `Rudin.Chapter11.ElementaryCharge.germ_add`, `Rudin.Chapter11.ElementaryCharge.additive`, `Rudin.Chapter11.ElementaryCharge.φ_empty`, `Rudin.Chapter11.ElementaryCharge.finite_additivity`, `Rudin.Chapter11.ElementaryCharge.well_defined`, `Rudin.Chapter11.ElementaryCharge.not_germ_of_away`, `Rudin.Chapter11.ElementaryCharge.interval_prescriptions`, `Rudin.Chapter11.ElementaryCharge.intervals_elementary`, `Rudin.Chapter11.ElementaryCharge.singleton_value`, `Rudin.Chapter11.ElementaryCharge.zero_interval_prescriptions`, `Rudin.Chapter11.ElementaryCharge.zero_intervals_elementary`, `Rudin.Chapter11.ElementaryCharge.charge_nonneg`, `Rudin.Chapter11.ElementaryCharge.ofReal_charge`, `Rudin.Chapter11.ElementaryCharge.charge_formula`, `Rudin.Chapter11.ElementaryCharge.charge_interval_prescriptions`, `Rudin.Chapter11.ElementaryCharge.charge_zero_interval_prescriptions`, `Rudin.Chapter11.ElementaryCharge.charge_finite_additivity`, `Rudin.Chapter11.ElementaryCharge.charge_well_defined`, `Rudin.Chapter11.ElementaryCharge.charge_empty`, `Rudin.Chapter11.ElementaryCharge.closed_away_zero`, `Rudin.Chapter11.ElementaryCharge.compact_away_zero`, `Rudin.Chapter11.ElementaryCharge.closed_subset_compact`, `Rudin.Chapter11.ElementaryCharge.regular_implies_endpoint_regular`, `Rudin.Chapter11.ElementaryCharge.nonregular_endpoint`, `Rudin.Chapter11.ElementaryCharge.nonregular`, `Rudin.Chapter11.ElementaryCharge.dyadic_elementary`, `Rudin.Chapter11.ElementaryCharge.dyadic_disjoint`, `Rudin.Chapter11.ElementaryCharge.dyadic_union`, `Rudin.Chapter11.ElementaryCharge.dyadic_value`, `Rudin.Chapter11.ElementaryCharge.no_countable_extension`, `Rudin.Chapter11.ElementaryCharge.dyadic_charge_hasSum`, `Rudin.Chapter11.ElementaryCharge.no_extendedReal_countable_extension`.

<a id="r11e16"></a>
### 11.16 — Sine subsequences converge only on a null set
**Lean source:** [Exercise16.lean](../../Math/Rudin/Chapter11/Exercise16.lean).
**Inventory status:** Verified as stated.

**Statement.** Let $(n_k)$ be a strictly increasing sequence of positive integers. The exact pointwise convergence set

$$
E=\{x\in(-\pi,\pi):\sin(n_kx)\text{ converges to a finite real limit}\}
$$

is measurable and has Lebesgue measure zero. Its measurability holds for every natural-number frequency sequence, without the increasing or positivity assumptions.

**Proof.** Each $x\mapsto\sin(n_kx)$ is continuous and measurable. The measurable convergence-set theorem, intersected with $(-\pi,\pi)$, proves measurability of the exact set $E$; no exceptional points are removed from its definition. It has finite measure.

The cosine classes of positive integer frequencies on $[-\pi,\pi]$ have inner product $\pi$ at equal frequencies and zero otherwise, by the cosine product identity and the zero integrals of nonconstant integer-frequency cosines. Normalizing them gives an orthonormal family. Bessel's inequality makes the coefficients of the $L^2$ indicator of $E$ tend to zero. After identifying the classes with their literal representatives almost everywhere, this says

$$
\int_E\cos(rx)\,dx\longrightarrow0\quad(r\in\mathbb N,\ r\to\infty).
$$

Put $a_k=n_{2k+1}$ and $b_k=n_k$. On $E$, convergence of the sine sequence implies

$$
h_k(x)=(\sin(a_kx)-\sin(b_kx))^2\longrightarrow0.
$$

Since $0\le h_k\le4$ and $m(E)<\infty$, dominated convergence gives $\int_Eh_k\to0$. On the other hand,

$$
h_k(x)=1-\frac12\cos(2a_kx)-\frac12\cos(2b_kx)
-\cos((a_k-b_k)x)+\cos((a_k+b_k)x).
$$

Strict increase of the natural-number frequencies gives $n_k\ge k$ and $n_{2k+1}-n_k\ge k+1$. Thus all four cosine frequencies in this identity tend to infinity. Their set integrals tend to zero by the preceding Bessel argument, so $\int_Eh_k\to m(E)$. Uniqueness of limits gives $m(E)=0$. Finiteness of $m(E)$ ensures that a zero real-valued measure is indeed zero measure, not the default real value of infinity.

**Lean declarations:** `Rudin.Chapter11.exercise16_measurability`, `Rudin.Chapter11.exercise16_null_convergence_set`, `Rudin.Chapter11.CosineL2.memLp_cos`, `Rudin.Chapter11.CosineL2.cosine_ae`, `Rudin.Chapter11.CosineL2.integral_cosine_mul`, `Rudin.Chapter11.CosineL2.inner_cosine`, `Rudin.Chapter11.CosineL2.orthonormal_normalized`, `Rudin.Chapter11.CosineL2.tendsto_inner_cosine`, `Rudin.Chapter11.CosineL2.inner_cosine_indicator`, `Rudin.Chapter11.CosineL2.tendsto_setIntegral_cosine`.

<a id="r11e17"></a>
### 11.17 — Only finitely many uniformly positive sine frequencies
**Lean source:** [Exercise17.lean](../../Math/Rudin/Chapter11/Exercise17.lean).
**Inventory status:** Verified as stated.

**Statement.** If $E\subseteq(-\pi,\pi)$ is Lebesgue measurable with positive measure and $\delta>0$, then

$$
\{n\in\mathbb Z:\sin(nx)\ge\delta\text{ for every }x\in E\}
$$

is finite. The condition is pointwise on all of $E$, includes equality with $\delta$, and allows negative as well as positive integer frequencies. The formal assumption is null measurability, so arbitrary Lebesgue-measurable sets are included.

**Proof.** Since $E$ is contained in a bounded interval, $0<m(E)<\infty$. Apply the sine coefficient limit proved from Bessel's inequality in Exercise 13 to the actual $L^2$ indicator of $E$. With $c=\delta m(E)>0$, choose $N$ such that

$$
-c<\int_E\sin((k+1)x)\,dx<c\qquad(k\ge N).
$$

For any real frequency $t$ whose sine is at least $\delta$ on $E$, monotonicity of the integral gives

$$
c\le\int_E\sin(tx)\,dx.
$$

All integrals exist because sine is bounded and $E$ has finite measure. For a positive integer $n=k+1$ satisfying the pointwise condition, the upper bound above forces $k<N$. For a negative integer $n=-(k+1)$, oddness of sine makes its integral the negative of the positive-frequency integral; the lower bound above again forces $k<N$. Frequency zero is impossible because its integral is zero while $c>0$. Hence all admissible integers lie in the finite interval $[-N,N]$.

**Lean declarations:** `Rudin.Chapter11.exercise17_finite_frequencies`.

<a id="r11e18"></a>
### 11.18 — Schwarz equality and the missing zero case
**Lean source:** [Exercise18.lean](../../Math/Rudin/Chapter11/Exercise18.lean).
**Inventory status:** Verified refutation and correction.

**Statement.** For complex square-integrable functions $f,g$ on a measure space, the printed claim is

$$
\left|\int f\overline g\,d\mu\right|^2
=\left(\int|f|^2\,d\mu\right)\left(\int|g|^2\,d\mu\right)
\quad\Longleftrightarrow\quad
 g=cf\ \text{almost everywhere for some }c\in\mathbb C.
$$

The implication from proportionality to equality is valid, but the unrestricted reverse implication is false.

**Correction.** On an arbitrary measure space, the complete criterion is

$$
\left|\int f\overline g\,d\mu\right|^2
=\left(\int|f|^2\,d\mu\right)\left(\int|g|^2\,d\mu\right)
\quad\Longleftrightarrow\quad
 f=0\ \text{almost everywhere}\ \text{or}\ 
 g=cf\ \text{almost everywhere for some }c\in\mathbb C.
$$

Thus the printed equivalence holds if one adds the explicit assumption that $f$ is not zero almost everywhere. No finite-total-measure assumption is required. Square integrability in the file includes almost-everywhere strong measurability and finite $L^2$ seminorm.

**Proof.** First consider the one-point space $X=\{*\}$ with unit point mass, and take $f(*)=0$, $g(*)=1$. Both functions are square integrable: their squared-norm integrals are $0$ and $1$. The displayed equality is $0=0\cdot1$. But no scalar satisfies $1=c\cdot0$ at the point of full measure. This refutes the printed necessity even on a finite measure space.

For the correction, let $F,G$ denote the classes of $f,g$ in complex $L^2(\mu)$. Its inner product, with the convention that the first argument is conjugate-linear, gives

$$
\langle G,F\rangle=\int f\overline g\,d\mu,\qquad
\|F\|^2=\int|f|^2\,d\mu,\qquad
\|G\|^2=\int|g|^2\,d\mu.
$$

The products are integrable by the $L^2$ inner-product theorem. Equality in the squared formula is equivalent to $|\langle G,F\rangle|=\|F\|\|G\|$, because both sides are nonnegative. The standard equality criterion for Cauchy–Schwarz in an inner-product space states that this holds exactly when $F=0$ or $G=cF$ for some complex scalar. Equality of $L^2$ classes is precisely equality almost everywhere of representatives. This gives the corrected assertion and, when $f$ is not zero almost everywhere, the printed equivalence with that additional hypothesis.

For completeness, if $g=cf$ almost everywhere and $A=\int|f|^2\,d\mu$, then

$$
\int f\overline g\,d\mu=\overline c\,A,
\qquad \int|g|^2\,d\mu=|c|^2A.
$$

Both sides of Schwarz equality are therefore $|c|^2A^2$. If $f=0$ almost everywhere, both sides are zero for every $g\in L^2$. If $g=0$ almost everywhere, proportionality holds with $c=0$. These observations include the both-zero case and show why no zero-function case can be omitted.

**Lean declarations:** `exercise18_proportional_implies_equality`, `exercise18_original_counterexample`, `exercise18_of_not_ae_zero`, `exercise18`, `exercise18_L2`, `exercise18_inner_integral`, `exercise18_norm_sq_integral`.
